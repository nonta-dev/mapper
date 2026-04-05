#!/usr/bin/env python3

# tree_manager:
#   テキストベースでファイルツリーを出力し、そのテキストを編集して
#   ディレクトリ／ファイルの再配置・新規作成・コピー・リンク作成を行うツール。
#
# 想定言語:
#   Python で実装する。
#   主眼はファイル操作そのものではなく、入力フォーマットの解釈、検証、
#   実行計画の生成、安全な反映にある。
#
# 基本動作:
#   1. 標準出力へ現在のファイルツリーを出力できる。
#   2. 標準入力からツリー定義を受け取り、作業パス配下を更新できる。
#
# 作業パス:
#   - オプションで指定できる。
#   - 未指定時はカレントディレクトリを作業パスとする。
#   - 作業パス直下の .tree/ は予約ディレクトリとし、出力対象にも比較対象にも含めない。
#
# 出力フォーマット:
#   1行は以下の形式とする。
#     indent + escaped_name + optional(padding + attrs...)
#
#   各要素:
#   - indent
#       行頭の空白。
#       インデントの深さは厳密な桁数ではなく、直前の親候補より空白数が多ければ
#       「1段深い」とみなす。
#   - escaped_name
#       ディレクトリ名またはファイル名。
#       ディレクトリは末尾 / で表現する。
#       以下をエスケープ可能とする。
#         \\  バックスラッシュ
#         \   半角スペース
#         \#  シャープ
#         \+  プラス
#   - padding
#       名前部と属性部の区切りとして挿入する空白。
#       属性がある場合は、名前列の表示位置を揃えるために使用する。
#   - attrs
#       空白区切りの属性列。
#
# 出力時の属性:
#   - <inode>
#       その項目の inode 番号。
#   - s:<inode>
#       その項目がシンボリックリンクであることを示す。
#       inode はリンク先実体の inode を表す。
#   - ハードリンクについては通常項目として出力し、h:<inode> は付与しなくてよい。
#
# 出力順:
#   - 同一ディレクトリ内では名前順で固定する。
#
# 入力フォーマット:
#   入力は出力フォーマットを拡張したものとする。
#
# 入力時の追加ルール:
#   - 先頭行として ./ が必須。
#   - 行頭の未エスケープ # はコメント行とみなし、無視する。
#   - inode は省略可能。
#       省略時は新規作成とみなす。
#   - 属性部に操作を記述できる。
#
# 入力時の属性:
#   - <inode>
#       既存のディレクトリ／ファイルを inode で指定する。
#       一致する既存実体に対する再配置・改名・移動として扱う。
#   - s <inode>
#       指定 inode の実体を参照するシンボリックリンクを新規作成する。
#   - h <inode>
#       指定 inode の実体を参照するハードリンクを新規作成する。
#       ハードリンクはファイルのみ許可する。
#   - c <inode>
#       指定 inode の実体のコピーを新規作成する。
#       ディレクトリも許可し、その場合は再帰コピーとする。
#
# 新規作成:
#   - inode のないディレクトリは新規ディレクトリ作成とする。
#   - inode のないファイルは空ファイル作成とする。
#
# コメントアウトの意味:
#   - コメントアウトされたノード自体は無効とし、削除対象とする。
#   - ただし、その子ノードは独立に評価する。
#     親がコメントアウトされていても、子が有効行であれば有効ノードとして扱う。
#
# 妥当性検証:
#   入力取り込み時は、実ファイル操作の前に必ず全体を検証する。
#   エラーがあれば何も変更せず終了する。
#
# 検証エラーとする条件:
#   - ルート ./ が存在しない。
#   - 参照先 inode が既存ツリー内に存在しない。
#   - 同一ディレクトリ内に同名項目がある。
#   - ファイルノードが子を持つ。
#   - h の参照先がディレクトリである。
#   - 通常ノードとして同じ inode が複数回現れる。
#   - その他、木構造や属性解釈が不正である。
#
# 既存ツリーの扱い:
#   - 作業パス配下を走査し、.tree/ を除外して現在状態を把握する。
#   - inode と実体パスの対応表を作る。
#
# 反映方式:
#   入力反映時は、作業パス直下の .tree/ を退避用ディレクトリとして使う。
#
# 反映前処理:
#   - まず入力全体のパースと検証を完了させる。
#   - .tree/ 配下を空にする。
#   - 作業対象の既存ディレクトリ／ファイルを .tree/ に退避する。
#
# 反映処理順:
#   1. 再配置
#      - inode 付き通常ノードに対して、移動・改名・再配置を行う。
#   2. コピー
#      - c <inode> を処理する。
#   3. ハードリンク
#      - h <inode> を処理する。
#   4. シンボリックリンク
#      - s <inode> を処理する。
#
# 削除対象:
#   - 結果として使用されなかった既存物は .tree/ に残す。
#   - これらを削除候補として保全する。
#
# 失敗時の扱い:
#   - 途中失敗時は自動ロールバックしない。
#   - 失敗時点の状態と .tree/ 内の退避内容を残して停止する。
#   - 復旧しやすさを優先する。

from __future__ import annotations

import argparse
import os
import shutil
import stat
import sys
import unicodedata
from dataclasses import dataclass, field
from pathlib import Path


RESERVED_DIR = ".tree"
ORIGINAL_DIR = "original"
DELETED_DIR = "deleted"
VALID_ESCAPES = {"\\", " ", "#", "+"}
OUTPUT_INDENT = "  "
VERSION = "0.1.0"
OUTPUT_HEADER_LINES = [
    "",
    "# 出力フォーマット：",
    "#   ./                           ルートディレクトリ。",
    "#     name/  <inode>             ディレクトリ。",
    "#     name   <inode>             ファイル。",
    "#     name   <inode> s:<inode>   シンボリックリンク。s:参照元ファイル。",
    "#",
    "# 入力フォーマット（操作）：",
    "#   既存を維持：",
    "#     行をそのまま残す。",
    "#   移動：",
    "#     行、インデントを変更。。",
    "#   削除：",
    "#     行を削除する。（コメントアウトでもOK）",
    "#   コピー：",
    "#     name   c:<inode>",
    "#   シンボリックリンクを作成：",
    "#     name   s <inode>",
    "#   ハードリンクを作成：",
    "#     name   h <inode>",
    "#",
    "#  notes：",
    "#   - 先頭の有効行は ./ で始める",
    "#   - 子要素は親より深くインデントする",
    "#   - ディレクトリ名は / で終える",
    "#   - 属性（シンボリックリンク）は名前の後ろに空白区切りで書かれる",
    "#   - 出力に含まれる s:<inode> は、入力時は無視される",
    "#   - 行頭の # はコメント行として無視される",
    "#   - 名前中の空白, #, +, \\ は \\ でエスケープする",
    "#   - 削除されたディレクトリ／ファイルは、作業パス配下の .tree/deleted/ に残される",
    "",
]


class TreeManagerError(Exception):
    pass


@dataclass
class ParsedLine:
    line_no: int
    indent: int
    name: str
    attrs: list[str]


@dataclass
class SpecNode:
    line_no: int
    indent: int
    name: str
    is_dir: bool
    inode: int | None = None
    op: str | None = None
    op_target_inode: int | None = None
    parent: SpecNode | None = None
    children: list[SpecNode] = field(default_factory=list)

    def add_child(self, child: "SpecNode") -> None:
        child.parent = self
        self.children.append(child)

    @property
    def escaped_name(self) -> str:
        return escape_name(self.name)

    @property
    def relative_path(self) -> Path:
        if self.parent is None:
            return Path(".")
        parts: list[str] = []
        node: SpecNode | None = self
        while node is not None and node.parent is not None:
            parts.append(node.name.rstrip("/"))
            node = node.parent
        return Path(*reversed(parts))


@dataclass
class CurrentEntry:
    path: Path
    inode: int
    is_dir: bool
    is_symlink: bool
    link_target_inode: int | None = None
    is_dead_symlink: bool = False


def main() -> int:
    args = parse_args()
    work_path = args.path.resolve()
    if not work_path.is_dir():
        raise TreeManagerError(f"作業パスがディレクトリではありません: {work_path}")

    if sys.stdin.isatty():
        emit_tree(work_path, with_header=not args.simple)
    else:
        spec_text = sys.stdin.read()
        if spec_text.strip():
            apply_spec(work_path, spec_text)
        else:
            emit_tree(work_path, with_header=not args.simple)
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="ファイルツリー管理ツール")
    parser.add_argument(
        "-p",
        "--path",
        type=Path,
        default=Path.cwd(),
        help="作業パス。省略時はカレントディレクトリ",
    )
    parser.add_argument(
        "-v",
        "--version",
        action="version",
        version=f"%(prog)s {VERSION}",
        help="バージョンを表示して終了",
    )
    parser.add_argument(
        "-s",
        "--simple",
        action="store_true",
        help="ツリー出力時にフッタ（説明書）を付けない",
    )
    return parser.parse_args()


def emit_tree(work_path: Path, with_header: bool = True) -> None:
    entries = scan_current_tree(work_path)
    root_stat = work_path.stat()
    lines = build_output_lines(work_path, entries, root_stat.st_ino)
    for line in lines:
        print(line)
    if with_header:
        for line in OUTPUT_HEADER_LINES:
            print(line)

def build_output_lines(
    work_path: Path,
    entries: dict[Path, CurrentEntry],
    root_inode: int,
) -> list[str]:
    rows: list[tuple[int, str, list[str]]] = [(0, "./", [str(root_inode)])]
    for child in sorted(entries.values(), key=lambda entry: entry.path.name):
        if child.path.parent != work_path:
            continue
        collect_output_rows(child, entries, 1, rows)

    name_width = max(display_width((OUTPUT_INDENT * depth) + escape_name(name)) for depth, name, _ in rows)
    attr_widths = compute_attr_widths(rows)
    return [format_output_line(depth, name, attrs, name_width, attr_widths) for depth, name, attrs in rows]


def collect_output_rows(
    entry: CurrentEntry,
    entries: dict[Path, CurrentEntry],
    depth: int,
    rows: list[tuple[int, str, list[str]]],
) -> None:
    display_name = entry.path.name + ("/" if entry.is_dir and not entry.is_symlink else "")
    attrs = [str(entry.inode)]
    if entry.is_symlink:
        if entry.is_dead_symlink:
            attrs.append("s:deadlink")
        elif entry.link_target_inode is not None:
            attrs.append(f"s:{entry.link_target_inode}")
    rows.append((depth, display_name, attrs))

    if not entry.is_dir or entry.is_symlink:
        return

    children = [
        child
        for child in entries.values()
        if child.path.parent == entry.path
    ]
    for child in sorted(children, key=lambda item: item.path.name):
        collect_output_rows(child, entries, depth + 1, rows)

def compute_attr_widths(rows: list[tuple[int, str, list[str]]]) -> list[int]:
    max_columns = max((len(attrs) for _, _, attrs in rows), default=0)
    widths: list[int] = []
    for index in range(max_columns):
        widths.append(
            max(
                (
                    display_width(attrs[index])
                    for _, _, attrs in rows
                    if index < len(attrs)
                ),
                default=0,
            )
        )
    return widths


def format_attr(attr: str, width: int, align: str = "left") -> str:
    padding = max(0, width - display_width(attr))
    if align == "right":
        return (" " * padding) + attr
    return attr + (" " * padding)


def format_output_line(
    depth: int,
    name: str,
    attrs: list[str],
    name_width: int,
    attr_widths: list[int],
) -> str:
    indent = OUTPUT_INDENT * depth
    escaped = escape_name(name)
    left = f"{indent}{escaped}"
    if not attrs:
        return left
    parts = [left]
    parts.append(" " * max(1, name_width - display_width(left) + 1))
    for index, attr in enumerate(attrs):
        if index < len(attrs) - 1:
            parts.append(format_attr(attr, attr_widths[index], align="left"))
        else:
            parts.append(attr)
        if index < len(attrs) - 1:
            parts.append(" ")
    return "".join(parts)


def scan_current_tree(work_path: Path) -> dict[Path, CurrentEntry]:
    entries: dict[Path, CurrentEntry] = {}
    for child in sorted(work_path.iterdir(), key=lambda path: path.name):
        if child.name == RESERVED_DIR:
            continue
        scan_entry(child, entries)
    return entries


def scan_entry(path: Path, entries: dict[Path, CurrentEntry]) -> None:
    st = path.lstat()
    is_link = stat.S_ISLNK(st.st_mode)
    is_dir = path.is_dir() if not is_link else False
    link_target_inode = None
    is_dead_symlink = False
    if is_link:
        try:
            target = path.resolve(strict=True)
        except FileNotFoundError:
            is_dead_symlink = True
        else:
            link_target_inode = target.stat().st_ino
            is_dir = target.is_dir()
    entries[path] = CurrentEntry(
        path=path,
        inode=st.st_ino,
        is_dir=is_dir,
        is_symlink=is_link,
        link_target_inode=link_target_inode,
        is_dead_symlink=is_dead_symlink,
    )
    if is_dir and not is_link:
        for child in sorted(path.iterdir(), key=lambda item: item.name):
            scan_entry(child, entries)


def apply_spec(work_path: Path, spec_text: str) -> None:
    parsed_lines = parse_input(spec_text)
    root = build_tree(parsed_lines)
    current_entries = scan_current_tree(work_path)
    current_inode_map = {entry.inode: entry for entry in current_entries.values()}
    validate_tree(root, work_path, current_inode_map)
    plan = make_plan(root, work_path, current_inode_map)
    apply_plan(work_path, plan)


@dataclass
class Plan:
    root: SpecNode
    existing_nodes: list[SpecNode]
    new_nodes: list[SpecNode]
    op_nodes: list[SpecNode]
    desired_existing_inodes: set[int]
    active_inode_targets: dict[int, Path]


def make_plan(
    root: SpecNode,
    work_path: Path,
    current_inode_map: dict[int, CurrentEntry],
) -> Plan:
    del work_path
    existing_nodes: list[SpecNode] = []
    new_nodes: list[SpecNode] = []
    op_nodes: list[SpecNode] = []
    active_inode_targets: dict[int, Path] = {}

    for node in iter_nodes(root):
        if node is root:
            continue
        if node.op is not None:
            op_nodes.append(node)
            continue
        if node.inode is None:
            new_nodes.append(node)
            continue
        existing_nodes.append(node)
        active_inode_targets[node.inode] = node.relative_path

    existing_nodes.sort(key=lambda node: len(node.relative_path.parts))
    new_nodes.sort(key=lambda node: len(node.relative_path.parts))
    op_nodes.sort(key=lambda node: len(node.relative_path.parts))

    desired_existing_inodes = {node.inode for node in existing_nodes if node.inode is not None}
    if root.inode is not None:
        desired_existing_inodes.add(root.inode)
        active_inode_targets[root.inode] = Path(".")

    for node in op_nodes:
        if node.op_target_inode is None:
            raise TreeManagerError(f"{node.line_no}行目: 参照 inode がありません")
        if node.op_target_inode not in current_inode_map:
            raise TreeManagerError(
                f"{node.line_no}行目: 参照 inode が存在しません: {node.op_target_inode}"
            )
        if node.op_target_inode not in active_inode_targets:
            raise TreeManagerError(
                f"{node.line_no}行目: 参照 inode は入力内で有効な通常ノードとして定義してください: "
                f"{node.op_target_inode}"
            )

    return Plan(
        root=root,
        existing_nodes=existing_nodes,
        new_nodes=new_nodes,
        op_nodes=op_nodes,
        desired_existing_inodes=desired_existing_inodes,
        active_inode_targets=active_inode_targets,
    )


def apply_plan(work_path: Path, plan: Plan) -> None:
    reserved_root = work_path / RESERVED_DIR
    original_root = reserved_root / ORIGINAL_DIR
    deleted_root = reserved_root / DELETED_DIR

    prepare_reserved_dir(reserved_root, original_root, deleted_root)
    stage_existing_entries(work_path, original_root)

    for node in plan.existing_nodes:
        relocate_existing_node(work_path, original_root, node)

    prune_unwanted_entries(work_path, deleted_root, plan.desired_existing_inodes)

    for node in plan.new_nodes:
        create_new_node(work_path, node)

    for node in plan.op_nodes:
        apply_operation_node(work_path, node, plan.active_inode_targets)


def prepare_reserved_dir(reserved_root: Path, original_root: Path, deleted_root: Path) -> None:
    reserved_root.mkdir(exist_ok=True)
    for child in reserved_root.iterdir():
        if child.is_dir() and not child.is_symlink():
            shutil.rmtree(child)
        else:
            child.unlink()
    original_root.mkdir()
    deleted_root.mkdir()


def stage_existing_entries(work_path: Path, original_root: Path) -> None:
    for child in sorted(work_path.iterdir(), key=lambda path: path.name):
        if child.name == RESERVED_DIR:
            continue
        shutil.move(str(child), str(original_root / child.name))


def relocate_existing_node(work_path: Path, original_root: Path, node: SpecNode) -> None:
    if node.inode is None:
        raise TreeManagerError(f"{node.line_no}行目: inode なしノードを既存再配置として処理できません")

    current_paths = collect_old_inode_paths(work_path, original_root)
    source = current_paths.get(node.inode)
    if source is None:
        raise TreeManagerError(
            f"{node.line_no}行目: inode {node.inode} の現在位置を特定できません"
        )

    destination = work_path / node.relative_path
    if source == destination:
        return

    ensure_parent_dir(destination.parent)
    if destination.exists() or destination.is_symlink():
        if same_inode(source, destination):
            return
        raise TreeManagerError(f"{node.line_no}行目: 配置先が既に存在します: {destination}")

    shutil.move(str(source), str(destination))


def collect_old_inode_paths(work_path: Path, original_root: Path) -> dict[int, Path]:
    mapping: dict[int, Path] = {}
    for base in (work_path, original_root):
        if not base.exists():
            continue
        for child in sorted(base.iterdir(), key=lambda path: path.name):
            if base == work_path and child.name == RESERVED_DIR:
                continue
            scan_old_inode_paths(child, mapping)
    return mapping


def scan_old_inode_paths(path: Path, mapping: dict[int, Path]) -> None:
    st = path.lstat()
    mapping[st.st_ino] = path
    is_link = stat.S_ISLNK(st.st_mode)
    if path.is_dir() and not is_link:
        for child in sorted(path.iterdir(), key=lambda item: item.name):
            scan_old_inode_paths(child, mapping)


def prune_unwanted_entries(
    work_path: Path,
    deleted_root: Path,
    desired_existing_inodes: set[int],
) -> None:
    for child in sorted(work_path.iterdir(), key=lambda path: path.name):
        if child.name == RESERVED_DIR:
            continue
        prune_entry(child, work_path, deleted_root, desired_existing_inodes)


def prune_entry(
    path: Path,
    work_path: Path,
    deleted_root: Path,
    desired_existing_inodes: set[int],
) -> None:
    st = path.lstat()
    inode = st.st_ino
    is_link = stat.S_ISLNK(st.st_mode)
    if inode not in desired_existing_inodes:
        move_to_deleted(path, work_path, deleted_root)
        return
    if path.is_dir() and not is_link:
        for child in sorted(path.iterdir(), key=lambda item: item.name):
            prune_entry(child, work_path, deleted_root, desired_existing_inodes)


def move_to_deleted(path: Path, work_path: Path, deleted_root: Path) -> None:
    relative = path.relative_to(work_path)
    destination = deleted_root / relative
    ensure_parent_dir(destination.parent)
    if destination.exists() or destination.is_symlink():
        destination = unique_deleted_path(destination)
    shutil.move(str(path), str(destination))


def unique_deleted_path(path: Path) -> Path:
    counter = 1
    while True:
        candidate = path.with_name(f"{path.name}.{counter}")
        if not candidate.exists() and not candidate.is_symlink():
            return candidate
        counter += 1


def create_new_node(work_path: Path, node: SpecNode) -> None:
    destination = work_path / node.relative_path
    ensure_parent_dir(destination.parent)
    if destination.exists() or destination.is_symlink():
        raise TreeManagerError(f"{node.line_no}行目: 新規作成先が既に存在します: {destination}")
    if node.is_dir:
        destination.mkdir()
    else:
        destination.touch()


def apply_operation_node(
    work_path: Path,
    node: SpecNode,
    active_inode_targets: dict[int, Path],
) -> None:
    if node.op is None or node.op_target_inode is None:
        raise TreeManagerError(f"{node.line_no}行目: 不正な操作ノードです")

    destination = work_path / node.relative_path
    ensure_parent_dir(destination.parent)
    if destination.exists() or destination.is_symlink():
        raise TreeManagerError(f"{node.line_no}行目: 操作先が既に存在します: {destination}")

    source_relative = active_inode_targets[node.op_target_inode]
    source = work_path / source_relative
    if not source.exists() and not source.is_symlink():
        raise TreeManagerError(f"{node.line_no}行目: 参照元が存在しません: {source}")

    if node.op == "c":
        if source.is_dir() and not source.is_symlink():
            shutil.copytree(source, destination, symlinks=True)
        else:
            shutil.copy2(source, destination, follow_symlinks=False)
        return

    if node.op == "h":
        os.link(source, destination, follow_symlinks=False)
        return

    if node.op == "s":
        link_target = os.path.relpath(source, destination.parent)
        destination.symlink_to(link_target)
        return

    raise TreeManagerError(f"{node.line_no}行目: 未対応の操作です: {node.op}")


def validate_tree(root: SpecNode, work_path: Path, current_inode_map: dict[int, CurrentEntry]) -> None:
    current_root_inode = work_path.stat().st_ino
    if root.name != "./":
        raise TreeManagerError("先頭の有効行は ./ である必要があります")
    if root.inode is not None and root.inode != current_root_inode:
        raise TreeManagerError("ルート ./ の inode が作業パスと一致しません")
    if root.op is not None:
        raise TreeManagerError("ルート ./ に操作は指定できません")

    seen_existing_inodes: dict[int, SpecNode] = {}
    for node in iter_nodes(root):
        if node is root:
            continue

        if node.parent is None:
            raise TreeManagerError(f"{node.line_no}行目: 親を特定できません")
        if not node.parent.is_dir:
            raise TreeManagerError(f"{node.line_no}行目: 親がファイルです")
        if node.children and not node.is_dir:
            raise TreeManagerError(f"{node.line_no}行目: ファイルは子ノードを持てません")

        if node.op is not None and node.children:
            raise TreeManagerError(f"{node.line_no}行目: 操作ノードは子ノードを持てません")
        if node.op is not None and node.inode is not None:
            raise TreeManagerError(f"{node.line_no}行目: 操作ノードに inode は指定できません")

        if node.inode is not None:
            current = current_inode_map.get(node.inode)
            if current is None:
                raise TreeManagerError(
                    f"{node.line_no}行目: 指定 inode が既存ツリーに存在しません: {node.inode}"
                )
            if current.is_dir != node.is_dir:
                raise TreeManagerError(f"{node.line_no}行目: 種別が既存 inode と一致しません")
            previous = seen_existing_inodes.get(node.inode)
            if previous is not None:
                raise TreeManagerError(
                    f"{node.line_no}行目: 同じ inode が複数回使われています: {node.inode}"
                )
            seen_existing_inodes[node.inode] = node

        if node.op is not None:
            if node.op_target_inode is None:
                raise TreeManagerError(f"{node.line_no}行目: 操作対象 inode がありません")
            current = current_inode_map.get(node.op_target_inode)
            if current is None:
                raise TreeManagerError(
                    f"{node.line_no}行目: 参照先 inode が存在しません: {node.op_target_inode}"
                )
            if node.op == "h" and current.is_dir:
                raise TreeManagerError(f"{node.line_no}行目: ディレクトリにハードリンクは作れません")

        validate_unique_sibling_names(node)


def validate_unique_sibling_names(node: SpecNode) -> None:
    if not node.is_dir:
        return
    seen: set[str] = set()
    for child in node.children:
        normalized = child.name.rstrip("/")
        if normalized in seen:
            raise TreeManagerError(
                f"{child.line_no}行目: 同一ディレクトリ内に同名項目があります: {normalized}"
            )
        seen.add(normalized)


def iter_nodes(root: SpecNode):
    stack = [root]
    while stack:
        node = stack.pop()
        yield node
        stack.extend(reversed(node.children))


def build_tree(parsed_lines: list[ParsedLine]) -> SpecNode:
    if not parsed_lines:
        raise TreeManagerError("入力が空です")

    root_line = parsed_lines[0]
    if root_line.name != "./":
        raise TreeManagerError("先頭の有効行は ./ である必要があります")

    root = build_node(root_line)
    stack: list[SpecNode] = [root]
    for parsed in parsed_lines[1:]:
        node = build_node(parsed)
        while stack and parsed.indent <= stack[-1].indent:
            stack.pop()
        if not stack:
            raise TreeManagerError(f"{parsed.line_no}行目: 親を決定できないインデントです")
        stack[-1].add_child(node)
        stack.append(node)
    return root


def build_node(parsed: ParsedLine) -> SpecNode:
    name = parsed.name
    is_dir = name == "./" or name.endswith("/")
    inode: int | None = None
    op: str | None = None
    op_target_inode: int | None = None

    if parsed.attrs:
        first = parsed.attrs[0]
        if first.isdigit():
            inode = int(first)
            rest = parsed.attrs[1:]
        else:
            rest = parsed.attrs
    else:
        rest = []

    rest = [token for token in rest if not is_output_only_attr(token)]

    if rest:
        if len(rest) != 2 or rest[0] not in {"s", "h", "c"} or not rest[1].isdigit():
            raise TreeManagerError(f"{parsed.line_no}行目: 属性の書式が不正です")
        op = rest[0]
        op_target_inode = int(rest[1])

    return SpecNode(
        line_no=parsed.line_no,
        indent=parsed.indent,
        name=name,
        is_dir=is_dir,
        inode=inode,
        op=op,
        op_target_inode=op_target_inode,
    )


def parse_input(spec_text: str) -> list[ParsedLine]:
    parsed: list[ParsedLine] = []
    for line_no, raw_line in enumerate(spec_text.splitlines(), start=1):
        if not raw_line.strip():
            continue
        if raw_line.lstrip(" ").startswith("#"):
            continue
        parsed.append(parse_line(raw_line, line_no))
    return parsed


def parse_line(raw_line: str, line_no: int) -> ParsedLine:
    indent = count_indent(raw_line)
    content = raw_line[indent:]
    name_part, attrs_part = split_name_and_attrs(content, line_no)
    if not name_part:
        raise TreeManagerError(f"{line_no}行目: 名前がありません")
    name = unescape_name(name_part, line_no)
    attrs = attrs_part.split() if attrs_part is not None and attrs_part else []
    return ParsedLine(line_no=line_no, indent=indent, name=name, attrs=attrs)


def count_indent(line: str) -> int:
    count = 0
    for char in line:
        if char == " ":
            count += 1
            continue
        if char == "\t":
            raise TreeManagerError("タブ文字によるインデントは未対応です")
        break
    return count


def split_name_and_attrs(content: str, line_no: int) -> tuple[str, str | None]:
    escaped = False
    for index, char in enumerate(content):
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if char == " ":
            attrs = content[index:].strip()
            if attrs.startswith("+ "):
                attrs = attrs[2:].strip()
            return content[:index], attrs or None
    if escaped:
        raise TreeManagerError(f"{line_no}行目: 不正なエスケープです")
    return content, None


def unescape_name(value: str, line_no: int) -> str:
    result: list[str] = []
    escaped = False
    for char in value:
        if escaped:
            if char not in VALID_ESCAPES:
                raise TreeManagerError(f"{line_no}行目: 未対応のエスケープです: \\{char}")
            result.append(char)
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        result.append(char)
    if escaped:
        raise TreeManagerError(f"{line_no}行目: 行末のエスケープが不正です")
    return "".join(result)


def escape_name(value: str) -> str:
    result: list[str] = []
    for char in value:
        if char in {"\\", " ", "#", "+"}:
            result.append("\\")
        result.append(char)
    return "".join(result)


def is_output_only_attr(token: str) -> bool:
    if token == "s:deadlink":
        return True
    if ":" not in token:
        return False
    prefix, value = token.split(":", 1)
    return prefix in {"s", "h"} and value.isdigit()


def display_width(value: str) -> int:
    width = 0
    for char in value:
        if unicodedata.combining(char):
            continue
        if unicodedata.east_asian_width(char) in {"F", "W"}:
            width += 2
        else:
            width += 1
    return width


def ensure_parent_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def same_inode(left: Path, right: Path) -> bool:
    try:
        return left.lstat().st_ino == right.lstat().st_ino
    except FileNotFoundError:
        return False


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except TreeManagerError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
