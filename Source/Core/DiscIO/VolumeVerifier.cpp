// Copyright 2019 Dolphin Emulator Project
// SPDX-License-Identifier: GPL-2.0-or-later

#include "DiscIO/VolumeVerifier.h"

#include <algorithm>
#include <future>
#include <memory>
#include <optional>
#include <string>
#include <string_view>

#include <mbedtls/md5.h>
#include <mz.h>
#include <mz_strm.h>
#include <mz_zip.h>
#include <mz_zip_rw.h>
#include <pugixml.hpp>

#include "Common/Align.h"
#include "Common/Assert.h"
#include "Common/CPUDetect.h"
#include "Common/CommonPaths.h"
#include "Common/CommonTypes.h"
#include "Common/Contains.h"
#include "Common/Crypto/SHA1.h"
#include "Common/FileUtil.h"
#include "Common/Hash.h"
#include "Common/HttpRequest.h"
#include "Common/IOFile.h"
#include "Common/Logging/Log.h"
#include "Common/MinizipUtil.h"
#include "Common/MsgHandler.h"
#include "Common/ScopeGuard.h"
#include "Common/StringUtil.h"
#include "Common/Swap.h"
#include "Common/Version.h"
#include "Core/IOS/Device.h"
#include "Core/IOS/ES/ES.h"
#include "Core/IOS/ES/Formats.h"
#include "Core/IOS/IOS.h"
#include "Core/IOS/IOSC.h"
#include "DiscIO/Blob.h"
#include "DiscIO/DiscScrubber.h"
#include "DiscIO/DiscUtils.h"
#include "DiscIO/Enums.h"
#include "DiscIO/Filesystem.h"
#include "DiscIO/Volume.h"
#include "DiscIO/VolumeWii.h"

namespace DiscIO
{
RedumpVerifier::DownloadState RedumpVerifier::m_gc_download_state;
RedumpVerifier::DownloadState RedumpVerifier::m_wii_download_state;

void RedumpVerifier::Start(const Volume& volume)
{
  if (!volume.IsDatelDisc())
  {
    m_game_id = volume.GetGameID();
    if (m_game_id.size() > 4)
      m_game_id = m_game_id.substr(0, 4);
  }

  m_revision = volume.GetRevision().value_or(0);
  m_disc_number = volume.GetDiscNumber().value_or(0);
  m_size = volume.GetDataSize();

  const Platform platform = volume.GetVolumeType();

  m_future = std::async(std::launch::async, [this, platform]() -> std::vector<PotentialMatch> {
    std::string system;
    DownloadState* download_state;
    switch (platform)
    {
    case Platform::GameCubeDisc:
      system = "gc";
      download_state = &m_gc_download_state;
      break;

    case Platform::WiiDisc:
      system = "wii";
      download_state = &m_wii_download_state;
      break;

    default:
      m_result.status = Status::Error;
      return {};
    }

    {
      std::lock_guard lk(download_state->mutex);
      download_state->status = DownloadDatfile(system, download_state->status);
    }

    switch (download_state->status)
    {
    case DownloadStatus::FailButOldCacheAvailable:
      ERROR_LOG_FMT(DISCIO, "Failed to fetch data from Redump.info, using old cached data instead");
      [[fallthrough]];
    case DownloadStatus::Success:
      return ScanDatfile(ReadDatfile(system), system);

    case DownloadStatus::Fail:
    default:
      m_result = {Status::Error, Common::GetStringT("Failed to connect to Redump.info")};
      return {};
    }
  });
}

static std::string GetPathForSystem(const std::string& system)
{
  return File::GetUserPath(D_REDUMPCACHE_IDX) + DIR_SEP + system + ".zip";
}

RedumpVerifier::DownloadStatus RedumpVerifier::DownloadDatfile(const std::string& system,
                                                               DownloadStatus old_status)
{
  if (old_status == DownloadStatus::Success)
    return old_status;

  Common::HttpRequest request;

  const std::optional<std::vector<u8>> result =
      request.Get("https://redump.info/datfile/" + system + "/serial,version",
                  {{"User-Agent", Common::GetEmulatorName()}});

  const std::string output_path = GetPathForSystem(system);

  if (!result)
  {
    return File::Exists(output_path) ? DownloadStatus::FailButOldCacheAvailable :
                                       DownloadStatus::Fail;
  }

  if (result->size() > 1 && (*result)[0] == '<' && (*result)[1] == '!')
  {
    // This is an HTML page, not a zip file like we want
    return File::Exists(output_path) ? DownloadStatus::FailButOldCacheAvailable :
                                       DownloadStatus::Fail;
  }

  File::CreateFullPath(output_path);
  if (!File::IOFile(output_path, "wb").WriteBytes(result->data(), result->size()))
    ERROR_LOG_FMT(DISCIO, "Failed to write downloaded datfile to {}", output_path);
  return DownloadStatus::Success;
}

std::vector<u8> RedumpVerifier::ReadDatfile(const std::string& system)
{
  void* zip_reader = mz_zip_reader_create();
  if (!zip_reader)
    return {};

  Common::ScopeGuard file_guard{[&] { mz_zip_reader_delete(&zip_reader); }};

  if (mz_zip_reader_open_file(zip_reader, GetPathForSystem(system).c_str()) != MZ_OK)
    return {};

  // Check that the zip file contains exactly one file
  if (mz_zip_reader_goto_first_entry(zip_reader) != MZ_OK)
    return {};
  if (mz_zip_reader_goto_next_entry(zip_reader) != MZ_END_OF_LIST)
    return {};

  // Read the file
  if (mz_zip_reader_goto_first_entry(zip_reader) != MZ_OK)
    return {};
  mz_zip_file* file_info;
  mz_zip_reader_entry_get_info(zip_reader, &file_info);
  std::vector<u8> data(file_info->uncompressed_size);
  if (!Common::ReadFileFromZip(zip_reader, data.data(), file_info->uncompressed_size))
    return {};

  return data;
}

static u8 ParseHexDigit(char c)
{
  if (c < '0')
    return 0;  // Error

  if (c >= 'a')
    c -= 'a' - 'A';
  if (c >= 'A')
    c -= 'A' - ('9' + 1);
  c -= '0';

  if (c >= 0x10)
    return 0;  // Error

  return c;
}

static std::vector<u8> ParseHash(const char* str)
{
  std::vector<u8> hash;
  while (str[0] && str[1])
  {
    hash.push_back(static_cast<u8>(ParseHexDigit(str[0]) * 0x10 + ParseHexDigit(str[1])));
    str += 2;
  }
  return hash;
}

std::vector<RedumpVerifier::PotentialMatch> RedumpVerifier::ScanDatfile(std::span<const u8> data,
                                                                        const std::string& system)
{
  pugi::xml_document doc;
  if (!doc.load_buffer(data.data(), data.size()))
  {
    m_result = {Status::Error, Common::GetStringT("Failed to parse Redump.info data")};
    return {};
  }

  std::vector<PotentialMatch> potential_matches;
  bool serials_exist = false;
  bool versions_exist = false;
  const pugi::xml_node datafile = doc.child("datafile");
  for (const pugi::xml_node game : datafile.children("game"))
  {
    std::string version_string = game.child("version").text().as_string();
    if (!version_string.empty())
      versions_exist = true;

    // Strip out prefix (e.g. "v1.02" -> "02", "Rev 2" -> "2")
    const size_t last_non_numeric = version_string.find_last_not_of("0123456789");
    if (last_non_numeric != std::string::npos)
      version_string = version_string.substr(last_non_numeric + 1);

    const int version = version_string.empty() ? 0 : std::stoi(version_string);

    const std::string serials = game.child("serial").text().as_string();
    if (!serials.empty())
      serials_exist = true;

    // The revisions for Korean GameCube games whose four-char game IDs end in E are numbered from
    // 0x30 in ring codes and in disc headers, but Redump switched to numbering them from 0 in 2019.
    if (version % 0x30 != m_revision % 0x30)
      continue;

    if (serials.empty() || serials.starts_with("DS"))
    {
      // GC Datel discs have no serials in Redump, Wii Datel discs have serials like "DS000101"
      if (!m_game_id.empty())
        continue;  // Non-empty m_game_id means we're verifying a non-Datel disc
    }
    else
    {
      bool serial_match_found = false;

      // If a disc has multiple possible serials, they are delimited with ", ". We want to loop
      // through all the serials until we find a match, because even though they normally only
      // differ in the region code at the end (which we don't care about), there is an edge case
      // disc with the game ID "G96P" and the serial "DL-DOL-D96P-EUR, DL-DOL-G96P-EUR".
      for (const std::string& serial_str : SplitString(serials, ','))
      {
        const std::string_view serial = StripWhitespace(serial_str);

        // Skip the prefix, normally either "DL-DOL-" or "RVL-" (depending on the console),
        // but there are some exceptions like the "RVLE-SBSE-USA-B0" serial.
        const size_t first_dash = serial.find_first_of('-', 3);
        const size_t game_id_start =
            first_dash == std::string::npos ? std::string::npos : first_dash + 1;

        if (game_id_start == std::string::npos || serial.size() < game_id_start + 4)
        {
          ERROR_LOG_FMT(DISCIO, "Invalid serial in redump datfile: {}", serial_str);
          continue;
        }

        const std::string_view game_id = serial.substr(game_id_start, 4);
        if (game_id != m_game_id)
          continue;

        u8 disc_number = 0;
        if (serial.size() > game_id_start + 5 && serial[game_id_start + 5] >= '0' &&
            serial[game_id_start + 5] <= '9')
        {
          disc_number = serial[game_id_start + 5] - '0';
        }
        if (disc_number != m_disc_number)
          continue;

        serial_match_found = true;
        break;
      }
      if (!serial_match_found)
        continue;
    }

    PotentialMatch& potential_match = potential_matches.emplace_back();
    const pugi::xml_node rom = game.child("rom");
    potential_match.size = rom.attribute("size").as_ullong();
    potential_match.hashes.crc32 = ParseHash(rom.attribute("crc").value());
    potential_match.hashes.md5 = ParseHash(rom.attribute("md5").value());
    potential_match.hashes.sha1 = ParseHash(rom.attribute("sha1").value());
  }

  if (!serials_exist || !versions_exist)
  {
    // If we reach this, the user has most likely downloaded a datfile manually,
    // so show a panic alert rather than just using ERROR_LOG

    // i18n: "Serial" refers to serial numbers, e.g. RVL-RSBE-USA
    PanicAlertFmtT(
        "Serial and/or version data is missing from {0}\n"
        "Please append \"{1}\" (without the quotes) to the datfile URL when downloading\n"
        "Example: {2}",
        GetPathForSystem(system), "serial,version", "http://redump.info/datfile/gc/serial,version");
    m_result = {Status::Error, Common::GetStringT("Failed to parse Redump.info data")};
    return {};
  }

  return potential_matches;
}

static bool HashesMatch(const std::vector<u8>& calculated, const std::vector<u8>& expected)
{
  return calculated.empty() || calculated == expected;
}

RedumpVerifier::Result RedumpVerifier::Finish(const Hashes<std::vector<u8>>& hashes)
{
  if (m_result.status == Status::Error)
    return m_result;

  if (hashes.crc32.empty() && hashes.md5.empty() && hashes.sha1.empty())
    return m_result;

  const std::vector<PotentialMatch> potential_matches = m_future.get();
  for (PotentialMatch p : potential_matches)
  {
    if (HashesMatch(hashes.crc32, p.hashes.crc32) && HashesMatch(hashes.md5, p.hashes.md5) &&
        HashesMatch(hashes.sha1, p.hashes.sha1) && m_size == p.size)
    {
      return {Status::GoodDump, Common::GetStringT("Good dump")};
    }
  }

  // We only return bad dump if there's a disc that we know this dump should match but that doesn't
  // match. For disc without IDs (i.e. Datel discs), we don't have a good way of knowing whether we
  // have a bad dump or just a dump that isn't in Redump, so we always pick unknown instead of bad
  // dump for those to be on the safe side. (Besides, it's possible to dump a Datel disc correctly
  // and have it not match Redump if you don't use the same replacement value for bad sectors.)
  if (!potential_matches.empty() && !m_game_id.empty())
    return {Status::BadDump, Common::GetStringT("Bad dump")};

  return {Status::Unknown, Common::GetStringT("Unknown disc")};
}

constexpr u64 DEFAULT_READ_SIZE = 0x20000;  // Arbitrary value

VolumeVerifier::VolumeVerifier(const Volume& volume, bool redump_verification,
                               Hashes<bool> hashes_to_calculate)
    : m_volume(volume), m_redump_verification(false),  // CDFREE: Always disable redump verification
      m_hashes_to_calculate(hashes_to_calculate),
      m_calculating_any_hash(hashes_to_calculate.crc32 || hashes_to_calculate.md5 ||
                             hashes_to_calculate.sha1),
      m_max_progress(volume.GetDataSize()), m_data_size_type(volume.GetDataSizeType())
{
  if (!m_calculating_any_hash)
    m_redump_verification = false;
}

VolumeVerifier::~VolumeVerifier()
{
  WaitForAsyncOperations();
}

Hashes<bool> VolumeVerifier::GetDefaultHashesToCalculate()
{
  Hashes<bool> hashes_to_calculate{.crc32 = true, .md5 = true, .sha1 = true};
  // If the system can compute certain hashes faster than others, only default-enable the fast ones.
  const bool sha1_hw_accel = Common::SHA1::CreateContext()->HwAccelerated();
  // For crc32, we assume zlib-ng will be fast if cpu supports crc32
  const bool crc32_hw_accel = cpu_info.bCRC32;
  if (crc32_hw_accel || sha1_hw_accel)
  {
    hashes_to_calculate.crc32 = crc32_hw_accel;
    // md5 has no accelerated implementation at the moment, always default to off
    hashes_to_calculate.md5 = false;
    // Always enable SHA1, to avoid situation where only crc32 is computed
    hashes_to_calculate.sha1 = true;
  }
  return hashes_to_calculate;
}

void VolumeVerifier::Start()
{
  ASSERT(!m_started);
  m_started = true;

  // CDFREE: Skip all verification - disable redump verification
  m_redump_verification = false;

  m_is_tgc = m_volume.GetBlobType() == BlobType::TGC;
  m_is_datel = m_volume.IsDatelDisc();
  m_is_triforce = m_volume.GetVolumeType() == Platform::Triforce;
  m_is_not_retail = (m_volume.GetVolumeType() == Platform::WiiDisc && !m_volume.HasWiiHashes()) ||
                    IsDebugSigned();

  // CDFREE: Skip partition checking - just proceed without validation
  std::vector<Partition> partitions;
  if (m_volume.GetVolumeType() == Platform::WiiWAD)
  {
    partitions = {};
  }
  else
  {
    partitions = m_volume.GetPartitions();
    if (partitions.empty())
    {
      // Try to get game partition even if invalid
      partitions = {m_volume.GetGamePartition()};
    }
  }

  if (IsDisc(m_volume.GetVolumeType()))
    m_biggest_referenced_offset = GetBiggestReferencedOffset(m_volume, partitions);

  // CDFREE: Skip CheckMisc() - don't validate game ID, region codes, IOS settings, etc.

  SetUpHashing();
}

std::vector<Partition> VolumeVerifier::CheckPartitions()
{
  // CDFREE: Return empty - skip partition validation
  return {};
}

bool VolumeVerifier::CheckPartition(const Partition& partition)
{
  // CDFREE: Skip partition checking
  return true;
}

std::string VolumeVerifier::GetPartitionName(std::optional<u32> type) const
{
  if (!type)
    return "???";

  std::string name = NameForPartitionType(*type, false);
  if (ShouldHaveMasterpiecePartitions() && *type > 0xFF)
  {
    return Common::FmtFormatT("{0} (Masterpiece)", name);
  }
  return name;
}

bool VolumeVerifier::IsDebugSigned() const
{
  const IOS::ES::TicketReader& ticket = m_volume.GetTicket(m_volume.GetGamePartition());
  return ticket.IsValid() ? ticket.GetConsoleType() == IOS::HLE::IOSC::ConsoleType::RVT : false;
}

bool VolumeVerifier::ShouldHaveChannelPartition() const
{
  static constexpr std::array<std::string_view, 18> channel_discs = {
      "RFNE01", "RFNJ01", "RFNK01", "RFNP01", "RFNW01", "RFPE01", "RFPJ01", "RFPK01", "RFPP01",
      "RFPW01", "RGWE41", "RGWJ41", "RGWP41", "RGWX41", "RMCE01", "RMCJ01", "RMCK01", "RMCP01",
  };
  static_assert(std::ranges::is_sorted(channel_discs));

  return std::ranges::binary_search(channel_discs, m_volume.GetGameID());
}

bool VolumeVerifier::ShouldHaveInstallPartition() const
{
  static constexpr std::array<std::string_view, 4> dragon_quest_x = {"S4MJGD", "S4SJGD", "S6TJGD",
                                                                     "SDQJGD"};
  const std::string& game_id = m_volume.GetGameID();
  return std::ranges::any_of(dragon_quest_x,
                             [&game_id](std::string_view x) { return x == game_id; });
}

bool VolumeVerifier::ShouldHaveMasterpiecePartitions() const
{
  static constexpr std::array<std::string_view, 4> ssbb = {"RSBE01", "RSBJ01", "RSBK01", "RSBP01"};
  const std::string& game_id = m_volume.GetGameID();
  return std::ranges::any_of(ssbb, [&game_id](std::string_view x) { return x == game_id; });
}

bool VolumeVerifier::ShouldBeDualLayer() const
{
  static constexpr std::array<std::string_view, 33> dual_layer_discs = {
      "R3ME01", "R3MP01", "R3OE01", "R3OJ01", "R3OP01", "RSBE01", "RSBJ01", "RSBK01", "RSBP01",
      "RXMJ8P", "S59E01", "S59JC8", "S59P01", "S5QJC8", "SAKENS", "SAKPNS", "SK8V52", "SK8X52",
      "SLSEXJ", "SLSP01", "SQIE4Q", "SQIP4Q", "SQIY4Q", "SR5E41", "SR5P41", "SUOE41", "SUOP41",
      "SVXX52", "SVXY52", "SX4E01", "SX4P01", "SZ3EGT", "SZ3PGT",
  };
  static_assert(std::ranges::is_sorted(dual_layer_discs));

  return std::ranges::binary_search(dual_layer_discs, m_volume.GetGameID());
}

void VolumeVerifier::CheckVolumeSize()
{
  // CDFREE: Skip volume size checks
}

void VolumeVerifier::CheckMisc()
{
  // CDFREE: Skip miscellaneous checks (game ID, region, IOS, etc.)
}

void VolumeVerifier::CheckSuperPaperMario()
{
  // CDFREE: Skip Super Paper Mario checks
}

void VolumeVerifier::SetUpHashing()
{
  if (m_volume.GetVolumeType() == Platform::WiiWAD)
  {
    m_content_offsets = m_volume.GetContentOffsets();
  }
  else if (m_volume.GetVolumeType() == Platform::WiiDisc)
  {
    m_scrubber.SetupScrub(m_volume);
  }

  std::ranges::sort(m_groups, {}, &GroupToVerify::offset);

  if (m_hashes_to_calculate.crc32)
    m_crc32_context = Common::StartCRC32();

  if (m_hashes_to_calculate.md5)
  {
    mbedtls_md5_init(&m_md5_context);
    mbedtls_md5_starts_ret(&m_md5_context);
  }

  if (m_hashes_to_calculate.sha1)
  {
    m_sha1_context = Common::SHA1::CreateContext();
  }
}

void VolumeVerifier::WaitForAsyncOperations() const
{
  if (m_crc32_future.valid())
    m_crc32_future.wait();
  if (m_md5_future.valid())
    m_md5_future.wait();
  if (m_sha1_future.valid())
    m_sha1_future.wait();
  if (m_content_future.valid())
    m_content_future.wait();
  if (m_group_future.valid())
    m_group_future.wait();
}

bool VolumeVerifier::ReadChunkAndWaitForAsyncOperations(u64 bytes_to_read)
{
  std::vector<u8> data(bytes_to_read);

  const u64 bytes_to_copy = std::min(m_excess_bytes, bytes_to_read);
  if (bytes_to_copy > 0)
    std::memcpy(data.data(), m_data.data() + m_data.size() - m_excess_bytes, bytes_to_copy);
  bytes_to_read -= bytes_to_copy;

  if (bytes_to_read > 0)
  {
    if (!m_volume.Read(m_progress + bytes_to_copy, bytes_to_read, data.data() + bytes_to_copy,
                       PARTITION_NONE))
    {
      return false;
    }
  }

  WaitForAsyncOperations();
  m_data = std::move(data);
  return true;
}

void VolumeVerifier::Process()
{
  ASSERT(m_started);
  ASSERT(!m_done);

  if (m_progress >= m_max_progress)
    return;

  // CDFREE: Minimal processing - just progress through the disc
  m_progress = m_max_progress;
}

u64 VolumeVerifier::GetBytesProcessed() const
{
  return m_progress;
}

u64 VolumeVerifier::GetTotalBytes() const
{
  return m_max_progress;
}

void VolumeVerifier::Finish()
{
  if (m_done)
    return;
  m_done = true;

  WaitForAsyncOperations();

  // CDFREE: Skip all verification - just return success
  m_result.summary_text = Common::GetStringT("CDFREE Mode: Verification disabled - File loaded without validation");
}

const VolumeVerifier::Result& VolumeVerifier::GetResult() const
{
  return m_result;
}

void VolumeVerifier::AddProblem(Severity severity, std::string text)
{
  // CDFREE: Don't add problems - skip all validation errors
}

}  // namespace DiscIO
