"""Build the read-only frozen C implementation; this is observation, not proof.

Usage: python3 experiments/run_f51_onebacking_probe.py COMPILER_CHECKOUT OUTPUT_DIR
No Compiler files are changed. No CMake/LLVM or native-source claim is made.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

compiler = Path(sys.argv[1]).resolve()
output = Path(sys.argv[2]).resolve()
head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=compiler, text=True).strip()
assert head == "4bc6b690e87b4646596dfd460bea26e9a5d8dac5", head
output.mkdir(parents=True, exist_ok=True)
probe = Path(__file__).with_name("f51_onebacking_probe.c").resolve()
# Unchanged CMakeLists.txt newlang_{semantic,checked,parser,syntax,lexer,source,diagnostic} lists.
units = "diagnostic source lexer syntax parser checked semantic semantic_check recursive_type allocated_node allocated_join captured_closure packet_fork fixed_field sum raw_storage function_body typed_owner transitive_terminal custody control".split()
binary = output / "f51_onebacking_probe"
flags = ["NEWLANG_EXPERIMENTAL_ORIGINAL_GRANT", "NEWLANG_EXPERIMENTAL_NESTED_CALLER",
         "NEWLANG_EXPERIMENTAL_TRANSITIVE_TERMINAL"]
subprocess.run(["gcc", "-std=c17", "-O0", "-g", "-Wall", "-Wextra", "-Wpedantic", "-Werror",
                *["-D" + flag + "=1" for flag in flags],
                "-I" + str(compiler / "include"), "-I" + str(compiler / "src"),
                "-I" + str(compiler / "tests/support"), str(probe),
                *[str(compiler / "src" / (unit + ".c")) for unit in units],
                "-o", str(binary)], check=True)
fixture = compiler / "tests/fixtures/allocated_node_semantic.nl"
p278 = compiler / "tests/fixtures/experimental_transitive_returned_whole.nl"
first = subprocess.check_output([str(binary), str(fixture), str(p278)], text=True)
assert first == subprocess.check_output([str(binary), str(fixture), str(p278)], text=True)
result = {"compiler_head": head, "experimental_flags": flags,
          "fixture": str(fixture.relative_to(compiler)),
          "fixture_sha256": hashlib.sha256(fixture.read_bytes()).hexdigest(),
          "p278_registered_source": str(p278.relative_to(compiler)),
          "p278_source_sha256": hashlib.sha256(p278.read_bytes()).hexdigest(),
          "probe_sha256": hashlib.sha256(probe.read_bytes()).hexdigest(),
          "checks": json.loads(first),
          "scope": "C checker observations only; no native allocator or Lean source refinement"}
assert all(result["checks"].values())
print(json.dumps(result, ensure_ascii=False, indent=2))
