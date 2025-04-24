#!/usr/bin/env python3

# version [2025-03-14]

import os
import sys
import re
import shutil
from pathlib import Path

def main():
    # Check that path to a world folder is passed as an argument
    if len(sys.argv) < 2:
        print("ERROR: Please specify a world folder.", file=sys.stderr)
        return

    path = os.path.realpath(sys.argv[1])

    if not (path and os.path.exists(path)):
        print(f"ERROR: The specified world folder\n    {path}\ndoes not exist.", file=sys.stderr)
        return

    if not os.path.isdir(path):
        print(f"ERROR: The specified world folder\n    {path}\nis not recognized as a folder -- it appears to be a regular file.", file=sys.stderr)
        return

    world_lean_file = f"{path}.lean"
    if not os.path.exists(world_lean_file):
        print(f"ERROR: The specified world folder\n    {path}\ndoes not have an accompanying file\n    {world_lean_file}", file=sys.stderr)
        return

    world_path = os.path.dirname(path)
    world_name = os.path.basename(path)

    print("\n".join([
        "This script will make a number of changes to folder",
        f"    {path}",
        "and to the associated file",
        f"    {world_lean_file}",
        "It is recommended that you git commit all local",
        "changes before running the script."
    ]))

    response = input("Are you sure you want to proceed? (y/n): ")
    if response.lower() != 'y':
        return

    # Read names of existing level files and count them
    os.chdir(os.path.join(world_path, world_name))
    old_names = sorted([f for f in os.listdir('.') if f.startswith('L') and f.endswith('.lean')])

    number_of_files = len(old_names)

    # Rename level files
    print("Renaming files ...")
    new_names = old_names.copy()

    for n in range(number_of_files):
        # Remove .lean extension
        old_base_name = old_names[n][:-5]
        # Extract the part after L**_
        match = re.match(r'L[^_]*(_.*)?$', old_base_name)
        if match:
            temp_name = match.group(1) or ""
        else:
            temp_name = ""
        # Create new name
        new_names[n] = f"L{n+1:02d}{temp_name}.lean"

        # Display planned renaming scheme
        compstr = "===" if old_names[n] == new_names[n] else "-->"
        print(f"  {old_names[n]:<20} {compstr} {new_names[n]}")

    # Create temporary folder for renaming
    temp_dir = os.path.join(world_path, world_name, ".sofi-temp")
    os.makedirs(temp_dir, exist_ok=True)

    # First step: move to temp directory with new names
    for n in range(number_of_files):
        shutil.move(
            os.path.join(world_path, world_name, old_names[n]),
            os.path.join(temp_dir, new_names[n])
        )

    # Second step: move back from temp directory
    for n in range(number_of_files):
        shutil.move(
            os.path.join(temp_dir, new_names[n]),
            os.path.join(world_path, world_name, new_names[n])
        )

    # Remove temp directory
    os.rmdir(temp_dir)

    # Edit the level files -- update level numbers and imports
    for n in range(number_of_files):
        file_path = os.path.join(world_path, world_name, new_names[n])
        print(f"Updating {file_path} ...")

        # Read file content
        with open(file_path, 'r') as file:
            content = file.read()

        # Update World Name
        print("   Updating World Name ...")
        content = re.sub(r'^World.*$', f'World "{world_name}"', content, flags=re.MULTILINE)

        # Update level number
        print("   Updating level number ...")
        content = re.sub(r'^Level.*$', f'Level {n+1}', content, flags=re.MULTILINE)

        # Update imports
        print("   Updating imports ...")

        # Replace import of old level k with import of new level k, provided k < n
        for k in range(n):
            old_base_name = old_names[k][:-5]  # Remove .lean
            new_base_name = new_names[k][:-5]  # Remove .lean
            content = re.sub(
                fr'^import Game\.Levels\.{world_name}\.{old_base_name}\s*$',
                f'import Game.Levels.{world_name}.{new_base_name}',
                content,
                flags=re.MULTILINE
            )

        # Delete import of old level k if k > n
        for k in range(n+1, number_of_files):
            old_base_name = old_names[k][:-5]  # Remove .lean
            content = re.sub(
                fr'^import Game\.Levels\.{world_name}\.{old_base_name}\s*$',
                '',
                content,
                flags=re.MULTILINE
            )

        # In level 0, delete imports from current world.
        # In higher levels, replace first import of level from current world with import of level n-1.
        if n == 0:
            content = re.sub(
                fr'^import Game\.Levels\.{world_name}.*$',
                '',
                content,
                flags=re.MULTILINE
            )
        else:
            prev_level_base = new_names[n-1][:-5]  # Remove .lean
            # Find first occurrence and replace it
            pattern = fr'^import Game\.Levels\.{world_name}.*$'
            match = re.search(pattern, content, re.MULTILINE)
            if match:
                content = content[:match.start()] + \
                          f'import Game.Levels.{world_name}.{prev_level_base}' + \
                          content[match.end():]

        # Write updated content back to file
        with open(file_path, 'w') as file:
            file.write(content)

    # Update world_name.lean file
    world_lean_path = os.path.join(world_path, f"{world_name}.lean")
    print(f"Updating imports in {world_lean_path} ...")

    # Read file content
    with open(world_lean_path, 'r') as file:
        content = file.read()

    # Delete all existing imports
    content = re.sub(r'^import .*$', '', content, flags=re.MULTILINE)

    # Create new imports
    new_imports = ""
    for n in range(number_of_files):
        new_base_name = new_names[n][:-5]  # Remove .lean
        new_imports += f"import Game.Levels.{world_name}.{new_base_name}\n"

    # Add imports at the beginning of the file
    content = new_imports + content

    # Write updated content back to file
    with open(world_lean_path, 'w') as file:
        file.write(content)

    print("Done.")

if __name__ == "__main__":
    main()
