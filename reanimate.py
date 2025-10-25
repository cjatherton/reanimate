#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2025 Christopher Atherton <the8lack8ox@proton.me>
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the “Software”), to
# deal in the Software without restriction, including without limitation the
# rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
# sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
# THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
#

"""Convert anime videos to AV1/Opus format."""

__author__ = "Christopher Atherton <the8lack8ox@proton.me>"
__version__ = "1.0"
__license__ = "MIT"

import argparse
from dataclasses import dataclass
import datetime
from itertools import chain
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Optional, Tuple
import time
import zlib

SVT_AV1_ENC_OPTS = (
    "--enable-qm", "1",
    "--qm-min", "0",
    "--scd", "1",
    "--enable-tf", "0",
    "--enable-overlays", "1",
    "--tune", "0",
    "--scm", "1",
    "--sharpness", "1",
    "--enable-variance-boost", "1",
    "--variance-boost-strength", "3",
    "--variance-octile", "4",
)


def get_file_crc(path):
    """Get the CRC-32 of a file."""
    with path.open("rb") as f:
        crc = 0
        chunk = f.read(8192)
        while chunk:
            crc = zlib.crc32(chunk, crc)
            chunk = f.read(8192)
        return crc


def check_filename_crc(path):
    """Check file against CRC-32 in filename."""
    m = re.search(r"\[([0-9A-Fa-f]{8})\]", path.stem)
    if m:
        return int(m.group(1), 16) == get_file_crc(path)
    return None


class MatroskaTags:
    """Matroska tags generator."""

    def __init__(self, target_type, target_value):
        self.__xml = '<?xml version="1.0"?>\n'
        self.__xml += '<!-- <!DOCTYPE Tags SYSTEM "matroskatags.dtd"> -->\n'
        self.__xml += "<Tags>\n"
        self.__xml += "  <Tag>\n"
        self.__xml += "    <Targets>\n"
        self.__xml += f"      <TargetTypeValue>{target_value}</TargetTypeValue>\n"
        self.__xml += f"      <TargetType>{target_type}</TargetType>\n"
        self.__xml += "    </Targets>\n"

    def start_new_target(self, target_type, target_value):
        """Begin a new tag target."""
        self.__xml += "  </Tag>\n"
        self.__xml += "  <Tag>\n"
        self.__xml += "    <Targets>\n"
        self.__xml += f"      <TargetTypeValue>{target_value}</TargetTypeValue>\n"
        self.__xml += f"      <TargetType>{target_type}</TargetType>\n"
        self.__xml += "    </Targets>\n"

    def add_entry(self, field, value, lang=None):
        """Add a tag entry for the target being worked on."""
        self.__xml += "    <Simple>\n"
        self.__xml += f"      <Name>{field}</Name>\n"
        self.__xml += f"      <String>{value}</String>\n"
        if lang and lang != "und":
            self.__xml += f"      <TagLanguage>{lang}</TagLanguage>\n"
        self.__xml += "    </Simple>\n"

    def add_entry_multilang(self, field, values, langs):
        """Add a tag entry for multiple languages for the target being worked on."""
        for index, value in enumerate(values):
            if value:
                self.__xml += "    <Simple>\n"
                self.__xml += f"      <Name>{field}</Name>\n"
                self.__xml += f"      <String>{value}</String>\n"
                if index < len(langs) and langs[index] and langs[index] != "und":
                    self.__xml += f"      <TagLanguage>{langs[index]}</TagLanguage>\n"
                self.__xml += "    </Simple>\n"

    def finish(self):
        """Finalize the tags data."""
        self.__xml += "  </Tag>\n"
        self.__xml += "</Tags>\n"
        return self.__xml


class MultimediaExtractor:
    """Getting information about and extracting from a multimedia file."""

    @staticmethod
    def _get_ffprobe_tag(source, field):
        """Get the tag field from an FFprobe dict."""
        if "tags" in source:
            if field in source["tags"]:
                if source["tags"][field]:
                    return source["tags"][field]
        return None

    class Track:
        """Superclass for tracks embedded in multimedia file."""

        def __init__(self, path, probe, tid):
            self._path = path
            self.tid = tid
            self._stream_id = probe["index"]
            self._codec = probe["codec_name"]
            self.__codec_long = probe["codec_long_name"]
            self.name = MultimediaExtractor._get_ffprobe_tag(probe, "title")
            self.language = MultimediaExtractor._get_ffprobe_tag(probe, "language")

        def print(self):
            """Print information about this track."""
            if self.name:
                print("Name:", self.name)
            if self.language:
                print("Language:", self.language)
            print("Codec:", self.__codec_long)

    class VideoTrack(Track):
        """Information and conversion of video tracks in multimedia file."""

        def __init__(self, path, probe, tid):
            assert probe["codec_type"] == "video"
            super().__init__(path, probe, tid)
            self.__dim = (probe["width"], probe["height"])
            if "sample_aspect_ratio" in probe and probe["sample_aspect_ratio"] != '"N/A"':
                sar_str = probe["sample_aspect_ratio"].split(":")
                self.__sar = (int(sar_str[0]), int(sar_str[1]))
            else:
                self.__sar = (1, 1)
            if "display_aspect_ratio" in probe and probe["display_aspect_ratio"] != '"N/A"':
                dar_str = probe["display_aspect_ratio"].split(":")
                self.__dar = (int(dar_str[0]), int(dar_str[1]))
            else:
                self.__dar = None
            fps_str = probe["r_frame_rate"].split("/")
            self.__fps = (int(fps_str[0]), int(fps_str[1]))
            self.__profile = probe["profile"]

        def print(self):
            """Print information about this video track."""
            print(f"---- Video track (TID: {self.tid:2d}) ----------------------------------------------------")
            super().print()
            print("Profile:", self.__profile)
            print("Dimensions:", self.__dim[0], "x", self.__dim[1])
            if self.__sar and self.__sar != (1, 1):
                print("Display aspect ratio:", self.__dar[0], "x", self.__dar[1])
            print("Frame rate:", self.__fps[0], "/", self.__fps[1])

        def get_sample_aspect_ratio(self):
            return self.__sar

        def get_display_aspect_ratio(self):
            return self.__dar

        @dataclass
        class ConvertSettings:
            """Settings for converting video streams."""
            # Filtering (for FFmpeg)
            deinterlace: bool
            ivtc: bool
            nnedi: Optional[Path]
            crop: Optional[Tuple[int, int, int, int]]
            scale: Optional[Tuple[int, int]]
            denoise: bool
            bilateral: bool
            # Encoding parameters (for SVT-AV1)
            crf: int
            preset: int
            film_grain: int

        def convert(self, out_path, settings):
            """Convert video track to AV1."""
            filter_chain = ""
            if settings.nnedi:
                if settings.deinterlace:
                    filter_chain += f"nnedi=weights={settings.nnedi},"
                elif settings.ivtc:
                    filter_chain += f"fieldmatch=combmatch=full,nnedi=weights={settings.nnedi}:deint=interlaced,decimate,"
            elif settings.deinterlace:
                filter_chain += "yadif,"
            elif settings.ivtc:
                filter_chain += "fieldmatch=combmatch=full,yadif=deint=interlaced,decimate,"
            if settings.crop:
                filter_chain += f"crop={settings.crop[0]}:{settings.crop[1]}:{settings.crop[2]}:{settings.crop[3]},"
            if settings.scale:
                filter_chain += f"scale={settings.scale[0]}:{settings.scale[1]},"
            if settings.denoise:
                filter_chain += "hqdn3d=4.0:3.0:6.0:4.5,"
            if settings.bilateral:
                filter_chain += "bilateral=5:0.05,"

            filter_args = ["-vf", filter_chain[:-1]] if filter_chain else []
            keyint = math.floor(self.__fps[0] / self.__fps[1] * 10.0)
            out_path = out_path.with_suffix(".ivf")

            try:
                with subprocess.Popen(
                    [
                        "ffmpeg",
                        "-i", self._path,
                        "-map", f"0:{self._stream_id}",
                        *filter_args,
                        "-pix_fmt", "yuv420p10le",
                        "-f", "yuv4mpegpipe",
                        "-strict", "-1",
                        "-",
                    ],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.DEVNULL,
                ) as dec_proc:
                    subprocess.run(
                        [
                            "SvtAv1EncApp",
                            "--preset", str(settings.preset),
                            "--crf", str(settings.crf),
                            *SVT_AV1_ENC_OPTS,
                            "--keyint", str(keyint),
                            "--film-grain", str(settings.film_grain),
                            "--input", "stdin",
                            "--output", out_path,
                        ],
                        stdin=dec_proc.stdout,
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                        check=True,
                    )
            except subprocess.CalledProcessError as e:
                raise Exception(f"Problem converting video track with TID {self.tid} using SvtAv1EncApp") from e

            return out_path

    class AudioTrack(Track):
        """Information and decoding of audio tracks in multimedia file."""

        def __init__(self, path, probe, tid):
            assert probe["codec_type"] == "audio"
            super().__init__(path, probe, tid)
            self.channels = probe["channels"]
            if "channel_layout" in probe:
                self.__layout = probe["channel_layout"]
            else:
                self.__layout = f"{self.channels} channels"
            self.__sample_rate = int(probe["sample_rate"])

        def print(self):
            """Print information about this audio track."""
            print(f"---- Audio track (TID: {self.tid:2d}) ----------------------------------------------------")
            super().print()
            print("Channels:", self.__layout)
            print("Sample rate:", self.__sample_rate, "Hz")

        @dataclass
        class ConvertSettings:
            """Settings for converting audio streams."""
            bitrate: int
            downmix_stereo: bool

        def convert(self, out_path, settings):
            """Convert audio track to Opus."""
            downmix_arg = ("--downmix-stereo",) if settings.downmix_stereo else ()
            out_path = out_path.with_suffix(".opus")
            try:
                with subprocess.Popen(
                    [
                        "ffmpeg",
                        "-i", self._path,
                        "-map", f"0:{self._stream_id}",
                        "-f", "wav",
                        "-",
                    ],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.DEVNULL,
                ) as dec_proc:
                    subprocess.run(
                        [
                            "opusenc",
                            "--bitrate", str(settings.bitrate),
                            *downmix_arg,
                            "-", out_path,
                        ],
                        stdin=dec_proc.stdout,
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                        check=True,
                    )
            except subprocess.CalledProcessError as e:
                raise Exception(f"Problem converting audio track with TID {self.tid} using opusenc") from e
            return out_path

    class SubtitleTrack(Track):
        """Information about subtitle tracks in multimedia file."""

        def __init__(self, path, probe, tid: int):
            assert probe["codec_type"] == "subtitle"
            super().__init__(path, probe, tid)

        def print(self):
            """Print information about this subtitle track."""
            print(f"---- Subtitle track (TID: {self.tid:2d}) -------------------------------------------------")
            super().print()

        def extract(self, out_path):
            """Extract subtitle track."""
            if self._path.suffix.lower() in (".ass", ".srt"):
                return self._path
            match self._codec:
                case "ass":
                    out_path = out_path.with_suffix(".ass")
                case "subrip":
                    out_path = out_path.with_suffix(".srt")
                case _:
                    out_path = out_path.with_suffix(".mkv")
            try:
                subprocess.run(
                    [
                        "ffmpeg",
                        "-i", self._path,
                        "-map", f"0:{self.tid}",
                        "-scodec", "copy",
                        out_path,
                    ],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    check=True,
                )
            except subprocess.CalledProcessError as e:
                raise Exception(f"Problem while extracting subtitle track with TID {self.tid} using ffmpeg") from e
            return out_path

    def __init__(self, path, offset):
        self.path = path.resolve()

        ffprobe = subprocess.check_output(
            [
                "ffprobe",
                "-print_format", "json",
                "-show_format", "-show_streams", "-show_chapters",
                path,
            ],
            stderr=subprocess.DEVNULL,
        )
        probe_dict = json.loads(ffprobe)

        self.title = MultimediaExtractor._get_ffprobe_tag(probe_dict["format"], "title")
        self.tracks = {}
        self.video_tracks = {}
        self.audio_tracks = {}
        self.subtitle_tracks = {}
        self.attachment_cnt = 0

        for stream in probe_dict["streams"]:
            match stream["codec_type"]:
                case "video":
                    track = self.VideoTrack(self.path, stream, offset)
                    self.tracks[offset] = track
                    self.video_tracks[offset] = track
                    offset += 1
                case "audio":
                    track = self.AudioTrack(self.path, stream, offset)
                    self.tracks[offset] = track
                    self.audio_tracks[offset] = track
                    offset += 1
                case "subtitle":
                    track = self.SubtitleTrack(self.path, stream, offset)
                    self.tracks[offset] = track
                    self.subtitle_tracks[offset] = track
                    offset += 1
                case "attachment":
                    self.attachment_cnt += 1

        if probe_dict["format"]["format_name"] == "matroska,webm":
            self.has_chapters = bool(probe_dict["chapters"])
        else:
            self.has_chapters = False
            self.attachment_cnt = 0

    def extract_chapters(self, path):
        """Extract chapters from this multimedia file."""
        assert self.has_chapters
        with path.open("wb") as f:
            try:
                subprocess.run(
                    ["mkvextract", self.path, "chapters"],
                    stdout=f,
                    stderr=subprocess.DEVNULL,
                    check=True,
                )
            except subprocess.CalledProcessError as e:
                raise Exception(f"Problem extracting chapters from '{self.path}' using mkvextract") from e

    def extract_attachments(self, path):
        """Extract attachments from this multimedia file."""
        assert self.attachment_cnt > 0
        path.mkdir()
        try:
            subprocess.run(
                ["mkvextract", self.path, "attachments"] + [str(i) for i in range(1, self.attachment_cnt + 1)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                cwd=path,
                check=True,
            )
        except subprocess.CalledProcessError as e:
            raise Exception(f"Problem extracting attachments from '{self.path}' using mkvextract") from e
        return list(path.iterdir())


def check_dependencies():
    """Check for required dependencies."""
    tools = ("ffprobe", "ffmpeg", "SvtAv1EncApp", "opusenc", "mkvextract", "mkvmerge")
    missing = [tool for tool in tools if shutil.which(tool) is None]
    if missing:
        raise Exception(f"Missing dependencies: {', '.join(missing)}")


def prompt_overwrite(path, skip=False):
    """Prompt if user wants to overwrite file. Return True is file must not be overwritten."""
    if path.exists() and not skip:
        response = None
        while response not in ("", "y", "n"):
            print(f"File '{path}' already exists. Overwrite? (y/N): ", end="")
            response = input().lower()
        return response != "y"
    return False


def parse_cli(args=None):
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(description="convert anime videos to AV1/Opus format")
    parser.add_argument("input", nargs="+", type=Path, help="input file(s)", metavar="INPUT")
    parser.add_argument("output", type=Path, help="location to put output file", metavar="OUTPUT")
    parser.add_argument("-T", "--file-title", help="set title for output file (empty string removes title from first input)")
    parser.add_argument("-t", "--tracks", nargs="+", type=int, help="select tracks from input to include in output", metavar="TID")
    parser.add_argument("-e", "--defaults", nargs="+", type=int, help="set default tracks", metavar="TID")
    parser.add_argument("-n", "--names", nargs="+", type=str, help="set track names (empty string removes input name)", metavar="NAME")
    parser.add_argument("-l", "--languages", nargs="+", type=str, help="set track languages (use 'und' or empty string for unknown language)", metavar="LANG", )
    parser.add_argument("-a", "--attach-file", nargs="+", type=Path, help="add attachments to output", metavar="FILE")
    parser.add_argument("-c", "--chapters", type=Path, help="add chapters to output", metavar="FILE")
    parser.add_argument("-r", "--no-chapters", action="store_true", help="do not include chapters from first input file")
    parser.add_argument("-f", "--no-attachments", action="store_true", help="do not include attachments first input file")
    parser.add_argument("-m", "--no-names", action="store_true", help="do not use names from input file(s)")
    parser.add_argument("-w", "--overwrite", action="store_true", help="overwrite output file if it exists")
    parser.add_argument("-s", "--no-strict-crc", action="store_true", help="do not abort if detected CRC in filename fails check")
    parser.add_argument("-k", "--add-filename-crc", action="store_true", help="'XXXXXXXX' in the output file name will be replaced the CRC of the output file")

    parser_video = parser.add_argument_group("video processing")
    parser_video.add_argument("-q", "--crf", default=24, type=int, choices=range(1, 64), help="set CRF for SVT-AV1 encoder [default: 24]", metavar="CRF")
    parser_video.add_argument("-p", "--preset", default=3, type=int, choices=range(14), help="set preset for SVT-AV1 encoder [default: 3]", metavar="PRESET")
    parser_video.add_argument("-g", "--film-grain", default=0, type=int, choices=range(51), help="add synthetic film grain with SVT-AV1 encoder (0 for off) [default: 0]", metavar="GRAIN")

    parser_deintivtc = parser_video.add_mutually_exclusive_group()
    parser_deintivtc.add_argument("-D", "--deinterlace", action="store_true", help="deinterlace")
    parser_deintivtc.add_argument("-I", "--ivtc", action="store_true", help="perform inverse telecine")
    parser_video.add_argument("-N", "--nnedi", type=Path, help="use NNEDI for deinterlacing and IVTC", metavar="WEIGHTS_FILE")
    parser_video.add_argument("-C", "--crop", nargs=4, type=int, help="crop", metavar=("W", "H", "X", "Y"))
    parser_video.add_argument("-S", "--scale", nargs=2, type=int, help="scale", metavar=("W", "H"))
    parser_video.add_argument("-F", "--denoise", action="store_true", help="apply denoising filter")
    parser_video.add_argument("-B", "--bilateral", action="store_true", help="apply bilateral filter")

    parser_display = parser.add_argument_group("video display")
    parser_mutdisplay = parser_display.add_mutually_exclusive_group()
    parser_mutdisplay.add_argument("-A", "--display-aspect", nargs=2, type=int, help="set display aspect ratio", metavar=("W", "H"))
    parser_mutdisplay.add_argument("-P", "--pixel-aspect", nargs=2, type=int, help="set display pixel aspect ratio", metavar=("W", "H"))
    parser_mutdisplay.add_argument("-X", "--display-dimensions", nargs=2, type=int, help="set display dimensions", metavar=("W", "H"))

    parser_audio = parser.add_argument_group("audio processing")
    parser_audio.add_argument("-b", "--audio-bitrate", nargs="+", type=int, choices=range(6, 257), help="set audio bitrate (specify in audio track order) [default: auto]", metavar="KBPS")
    parser_audio.add_argument("-2", "--downmix-stereo", nargs="+", type=int, help="downmix audio to stereo (specify audio TIDs)", metavar="TID")

    parser_metadata = parser.add_argument_group("metadata")
    parser_metadata.add_argument("-M", "--movie-tags", action="store_true", help="use movie tag format (otherwise series is assumed)")
    parser_metadata.add_argument("--title", nargs="+", help="set title for series/movie")
    parser_metadata.add_argument("--season", type=int, help="set season number")
    parser_metadata.add_argument("--season-title", nargs="+", help="set season title")
    parser_metadata.add_argument("--episode", type=int, help="set episode number")
    parser_metadata.add_argument("--episode-title", nargs="+", help="set episode title")
    parser_metadata.add_argument("--episode-total", type=int, help="set episode total number")
    parser_metadata.add_argument("--studio", nargs="+", help="set animation studio name")
    parser_metadata.add_argument("--director", nargs="+", help="set director name")
    parser_metadata.add_argument("--screenplay", nargs="+", help="set screenplay writer name")
    parser_metadata.add_argument("--release-date", nargs=3, type=int, help="set release (or air) date", metavar=("YYYY", "MM", "DD"))
    parser_metadata.add_argument("--subber", nargs="+", help="set subtitle author name for subtitles")
    parser_metadata.add_argument("--content-type", nargs="+", help="override content type (i.e. Anime or アニメ)")
    parser_metadata.add_argument("-L", "--tag-language", nargs="+", help="set tag language(s), set more than one to add tags in multiple languages", metavar="LANG")

    return parser.parse_args(args)


def collect_inputs(inputs, strict_crc):
    """Examine inputs."""
    offset = 0
    extractors = []
    for input in inputs:
        print(f"Examining input file '{input}' ...")
        if not input.exists():
            raise FileNotFoundError(f"Input file '{input}' does not exist")
        crc_result = check_filename_crc(input)
        if crc_result is not None:
            if crc_result:
                print("==> CRC Check: OK")
            elif strict_crc:
                raise ValueError(f"CRC in filename for '{input}' is not valid")
            else:
                print("==> CRC Check: FAIL")
        extractor = MultimediaExtractor(input, offset)
        print("==> Title:", extractor.title if extractor.title else "(none)")
        print("==> Chapters:", "yes" if extractor.has_chapters else "no")
        print("==> Attachments:", extractor.attachment_cnt)
        offset += len(extractor.tracks)
        extractors.append(extractor)
    return extractors


def print_tracks(inputs):
    """Print track contents of input files."""
    print("Track information follows ...")
    for input in inputs:
        for track in input.tracks.values():
            track.print()
    print("-------------------------------------------------------------------------------")


def collect_tracks(inputs, requested):
    """Get tracks from inputs."""
    if requested is None:
        return list(chain.from_iterable(input.tracks.values() for input in inputs))
    return [next(input.tracks[tid] for input in inputs) for tid in requested]


def write_global_tags(cli, path):
    """Create global Matroska tags file."""
    tags = MatroskaTags("MOVIE", 50) if cli.movie_tags else MatroskaTags("COLLECTION", 70)
    if cli.title:
        tags.add_entry_multilang("TITLE", cli.title, cli.tag_language)
    if cli.content_type:
        tags.add_entry_multilang("CONTENT_TYPE", cli.content_type, cli.tag_language)
    else:
        tags.add_entry("CONTENT_TYPE", "アニメ", "ja")
        tags.add_entry("CONTENT_TYPE", "Anime", "en")
    if not cli.movie_tags and (cli.season_title or cli.season or cli.episode_total):
        tags.start_new_target("SEASON", 60)
        if cli.season_title:
            tags.add_entry_multilang("TITLE", cli.season_title, cli.tag_language)
        if cli.season:
            tags.add_entry("PART_NUMBER", cli.season)
        if cli.episode_total:
            tags.add_entry("TOTAL_PARTS", cli.episode_total)
    if cli.studio:
        tags.add_entry_multilang("PRODUCTION_STUDIO", cli.studio, cli.tag_language)
    if cli.director:
        tags.add_entry_multilang("DIRECTOR", cli.director, cli.tag_language)
    if not cli.movie_tags and (cli.episode_title or cli.episode):
        tags.start_new_target("EPISODE", 50)
        if cli.episode_title:
            tags.add_entry_multilang("TITLE", cli.episode_title, cli.tag_language)
        if cli.episode:
            tags.add_entry("PART_NUMBER", cli.episode)
    if cli.screenplay:
        tags.add_entry_multilang("SCREENPLAY_BY", cli.screenplay, cli.tag_language)
    if cli.release_date:
        tags.add_entry("RELEASE_DATE", f"{cli.release_date[0]:04d}-{cli.release_date[1]:02d}-{cli.release_date[2]:02d}")
    tags.add_entry("DATE_ENCODED", datetime.date.today().isoformat())
    tags.add_entry("COMMENT", "Support Anime by purchasing/streaming it when it's available in your region!", "en")
    path.write_text(tags.finish(), encoding="utf-8")


def get_title(cli, input):
    """Get title argument for mkvmerge."""
    if cli.file_title is not None:
        if len(cli.file_title) > 0:
            return ["--title", cli.file_title]
    elif input.title:
        return ["--title", input.title]
    return []


def get_chapters(cli, input, work_path):
    """Get chapters argument for mkvmerge."""
    if cli.chapters:
        if not cli.chapters.exists() or not cli.chapters.is_file():
            raise FileNotFoundError(f"Chapters file '{cli.chapters}' does not exist or is not a file")
        return ["--chapters", str(cli.chapters)]
    if not cli.no_chapters:
        if input.has_chapters:
            path = work_path / "chapters.xml"
            input.extract_chapters(path)
            return ["--chapters", str(path)]
        return []
    return []


def get_attachments(cli, input, work_path):
    """Get attachments argument for mkvmerge."""
    if cli.attach_file:
        ret = []
        for f in cli.attach_file:
            if not f.exists() or not f.is_file():
                raise FileNotFoundError(f"Attachment file '{f}' does not exist or is not a file")
            ret += ["--attach-file", str(f)]
        return ret
    if not cli.no_attachments:
        if input.attachment_cnt > 0:
            path = work_path / "attachments"
            attachments = input.extract_attachments(path)
            return [item for f in attachments for item in ("--attach-file", str(f))]
        return []
    return []


def get_global_tags(cli, work_path):
    """Get global tags for mkvmerge."""
    path = work_path / "global_tags.xml"
    write_global_tags(cli, path)
    return ["--global-tags", str(path)]


def get_track_name(cli, track):
    """Get name for track."""
    index = cli.tracks.index(track.tid) if cli.tracks else track.tid
    if cli.names is not None and index < len(cli.names):
        name = cli.names[index]
        return ["--track-name", f"0:{name}"] if name else []
    return ["--track-name", f"0:{track.name}"] if not cli.no_names and track.name else []


def get_track_language(cli, track):
    """Get language for track."""
    index = cli.tracks.index(track.tid) if cli.tracks else track.tid
    if cli.languages is not None and index < len(cli.languages):
        lang = cli.languages[index]
        return ["--language", f"0:{lang}"] if lang and lang != "und" else []
    return ["--language", f"0:{track.lang}"] if track.language and track.language != "und" else []


def get_default_track_flag(cli, tracks, track):
    """Set the default track flag for track."""
    if cli.defaults is not None:
        if track.tid in cli.defaults:
            return ["--default-track-flag", "0:1"]
    elif next(t for t in tracks if isinstance(t, type(track))) is track:
        return ["--default-track-flag", "0:1"]
    return ["--default-track-flag", "0:0"]


def get_track_tags(cli, tracks, track, work_path):
    """Get tags for output track."""
    if cli.subber is not None and isinstance(track, MultimediaExtractor.SubtitleTrack):
        i = [t.tid for t in tracks if isinstance(t, MultimediaExtractor.SubtitleTrack)].index(track.tid)
        if i < len(cli.subber):
            if cli.movie_tags:
                tags = MatroskaTags("MOVIE", 50)
            else:
                tags = MatroskaTags("SEASON", 60)
            tags.add_entry("WRITTEN_BY", cli.subber[i])
            path = work_path / f"tags_{track.tid:02d}.xml"
            path.write_text(tags.finish(), encoding="utf-8")
            return ["--tags", f"0:{path}"]
    return []


def get_video_display_settings(cli, track):
    """Get video display settings for track."""
    if cli.display_aspect:
        return ["--aspect-ratio", f"0:{cli.display_aspect[0]}/{cli.display_aspect[1]}"]
    if cli.pixel_aspect:
        return ["--aspect-ratio-factor", f"0:{cli.pixel_aspect[0]}/{cli.pixel_aspect[1]}"]
    if cli.display_dimensions:
        return ["--display-dimensions", f"0:{cli.display_dimensions[0]}x{cli.display_dimensions[1]}"]
    if track.get_sample_aspect_ratio() != (1, 1):
        w, h = track.get_display_aspect_ratio()
        return ["--aspect-ratio", f"0:{w}/{h}"]
    return []


def get_audio_settings(cli, tracks, track):
    """Get audio settings for track."""
    i = [t.tid for t in tracks if isinstance(t, MultimediaExtractor.AudioTrack)].index(track.tid)
    if cli.audio_bitrate and i < len(cli.audio_bitrate):
        bitrate = cli.audio_bitrate[i]
    elif track.channels == 1:
        bitrate = 96
    elif track.channels == 2 or track.tid in cli.downmix_stereo:
        bitrate = 128
    else:
        bitrate = 192
    return MultimediaExtractor.AudioTrack.ConvertSettings(bitrate, cli.downmix_stereo and track.channels > 2)


def convert(cli, inputs):
    """Convert the input files to the output file."""
    with tempfile.TemporaryDirectory(prefix=Path(__file__).stem + "-") as work_dir:
        print("Created work directory:", work_dir)
        work_path = Path(work_dir)
        mkvmerge_args = ["mkvmerge"]
        mkvmerge_args += get_title(cli, inputs[0])
        mkvmerge_args += get_chapters(cli, inputs[0], work_path)
        mkvmerge_args += get_attachments(cli, inputs[0], work_path)
        mkvmerge_args += get_global_tags(cli, work_path)
        mkvmerge_args += ["--output", str(cli.output)]

        video_settings = MultimediaExtractor.VideoTrack.ConvertSettings(
            cli.deinterlace,
            cli.ivtc,
            cli.nnedi,
            cli.crop,
            cli.scale,
            cli.denoise,
            cli.bilateral,
            cli.crf,
            cli.preset,
            cli.film_grain,
        )

        tracks = collect_tracks(inputs, cli.tracks)
        for track in tracks:
            mkvmerge_args += get_track_name(cli, track)
            mkvmerge_args += get_track_language(cli, track)
            mkvmerge_args += get_default_track_flag(cli, tracks, track)
            mkvmerge_args += get_track_tags(cli, tracks, track, work_path)
            match type(track):
                case MultimediaExtractor.VideoTrack:
                    print(f"Transcoding video track (TID: {track.tid}) ...")
                    path = work_path / f"video_{track.tid:02d}"
                    path = track.convert(path, video_settings)
                    mkvmerge_args += get_video_display_settings(cli, track)
                    mkvmerge_args.append(str(path))
                case MultimediaExtractor.AudioTrack:
                    audio_settings = get_audio_settings(cli, tracks, track)
                    if audio_settings.downmix_stereo:
                        print(f"Transcoding (stereo downmixing) audio track (TID: {track.tid}) @ {audio_settings.bitrate}kbps ...")
                    else:
                        print(f"Transcoding audio track (TID: {track.tid}) @ {audio_settings.bitrate}kbps ...")
                    path = work_path / f"audio_{track.tid:02d}"
                    path = track.convert(path, audio_settings)
                    mkvmerge_args.append(str(path))
                case MultimediaExtractor.SubtitleTrack:
                    path = work_path / f"subtitle_{track.tid:02d}"
                    path = track.extract(path)
                    print(f"Extracted subtitle track (TID: {track.tid}) ...")
                    mkvmerge_args.append(str(path))

        print("Writing output ...")
        try:
            subprocess.run(
                mkvmerge_args,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=True,
            )
        except subprocess.CalledProcessError as e:
            raise Exception("Problem merging Matroska file using mkvmerge") from e


def run(args=None):
    """Run routine."""
    # Some things
    check_dependencies()
    cli = parse_cli(args)
    if prompt_overwrite(cli.output, cli.overwrite):
        return
    inputs = collect_inputs(cli.input, not cli.no_strict_crc)
    print_tracks(inputs)

    # Convert
    print("Beginning process at", time.asctime(), "...")
    start_time = time.time()
    convert(cli, inputs)

    # Finished
    process_time = round(time.time() - start_time)
    print(
        "Finished! Process took",
        process_time // 60 // 60, "hours,",
        process_time // 60 % 60, "minutes, and",
        process_time % 60, "seconds.",
    )
    input_size = sum(input.stat().st_size for input in cli.input)
    output_size = cli.output.stat().st_size
    ratio = output_size / input_size
    print(f"Size difference: {output_size / 1048576:.1f} MiB / {input_size / 1048576:.1f} MiB = {ratio:.3f}")

    # Add CRC to filename if requested
    if cli.add_filename_crc:
        output_crc = get_file_crc(cli.output)
        new_name = cli.output.name.replace("XXXXXXXX", f"{output_crc:08X}")
        cli.output.rename(cli.output.with_name(new_name))


def main(argv=None):
    """Main routine (for processing errors)."""
    try:
        run(None if argv is None else argv[1:])
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        print("Exiting with failure ...")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
