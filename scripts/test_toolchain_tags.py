#!/usr/bin/env python3
"""Unit tests for scripts/toolchain_tags.py.

Run with: python3 scripts/test_toolchain_tags.py

No network. Upstream reads either go through a routed `core.gh_api` fake that rejects
any path it does not recognise, so adding a request shape is a deliberate act, or
through `FakeUpstream`, an offline model of the parts of mathlib's history this
repository's releases actually depend on.

The segment fixture below is the real (toolchain, pin) table of `main`, so base
derivation is pinned to real commits rather than to a story about them.
"""

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "pr_status"))
os.environ.setdefault("ZULIP_TOPIC", "Releases")

import core  # noqa: E402
import toolchain_tags as tt  # noqa: E402

# --- fixtures ----------------------------------------------------------------

# The real segments of main, oldest first, as of the commit that introduced this test:
# (first_index, last_index, toolchain, mathlib pin, first sha, last sha).
REAL_SEGMENTS_RAW = [
    (0, 120, "leanprover/lean4:v4.31.0-rc1",
     "66748b489336a59ed4b4a4a612615c38de823e9a",
     "818d32f10a29dbfdd0807ae88270cb3c48e8cff7", "d0660b2555379c5b09e6dbd829ace8d147d21f15"),
    (121, 131, "leanprover/lean4:v4.31.0-rc2",
     "0be66d77ba290828a5260d883ace636f56bce89a",
     "41ede0449b69dc5f5353b5db34642d3d1c58aad9", "19912f44a51669ab5d9302c247757862694bbf9f"),
    (132, 140, "leanprover/lean4:v4.31.0",
     "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f",
     "d2da4153396c7a2d57f3d068d194fb91468cfa40", "57a2df6a6ccfd83ce9e3a05123a927e4cdd6a340"),
    (141, 185, "leanprover/lean4:v4.31.0",
     "5ac74759704aa69e70b00ea2a622efd06aba73df",
     "154d23f2254b386c44a4ab415a027178f42cc822", "07f9e637e1c711da36ad37c6990bee790e6acdcc"),
    (186, 210, "leanprover/lean4:v4.31.0",
     "63b065c2a061e7286444690d8c427f79cd6d5b6d",
     "20065580dabf242e5989c98b3ba9f74f05e65424", "b04120e2f4927bde9624602e84833cdc8b5661f9"),
    (211, 239, "leanprover/lean4:v4.32.0-rc1",
     "843d7890de006fe2cb1d2974f5bafcf1b0e3fad8",
     "eb7d34820ada29e2cf84508aaf7ea095f1fc1a2b", "4178d1e340a824cbdee895cfcc087c48bd78cb24"),
    (240, 272, "leanprover/lean4:v4.32.0-rc1",
     "29af5245bafea7d69fdca69591450f60b916ed71",
     "76e25d1820a2114f8101b3f3e68dec4b3dd6a0d3", "98d424abef6fa2ef970b03aa9bd5c5171baa71b3"),
    (273, 324, "leanprover/lean4:v4.32.0-rc1",
     "06e4a530c2ee8e5c0fc6ba40a38d4814102c8fa2",
     "c856c23ccc33137dadb3c916caba885d324a009a", "324fc42e579082a715be52fcd6f58373046b7421"),
    (325, 350, "leanprover/lean4:v4.32.0-rc1",
     "a163fd2f6fb7408d4102dbb5faaca2b635ba1c0d",
     "f4dabe1db623670ea3d36f8f8efd4aecfc5f29f3", "41877a33b24abce37ae068424f0300e7f280aa26"),
    (351, 374, "leanprover/lean4:v4.32.0-rc1",
     "9ca31d8b72cf8c317e49c301bfdbfbe91fc49136",
     "54895e9dcd668aaddd9b90c0784b450614fa4c20", "19a60cf0f738af696f969328211571947e6eba83"),
    (375, 404, "leanprover/lean4:v4.32.0-rc1",
     "2929a789898c9465220a5e2361032eb9edc5c928",
     "c484d4cf76ea5e2186672da58a5ced7acacdb6c8", "d23d61874d5edfd82dc684153a96717b4ed4244c"),
    (405, 425, "leanprover/lean4:v4.32.0-rc1",
     "571b8a8e54219b4d393f75f4b8653fac08197fcc",
     "1d97fc27f45b10f9610386500b1cc09a5a3a1645", "3236707714564e353403c16ea827a369a732b2f7"),
    (426, 449, "leanprover/lean4:v4.32.0-rc1",
     "0f320b07b214a5ce015b3da2cac08946c4b5a506",
     "5cbc6442b19f075a3328f0e1565541d1ca86ede1", "f917d544f12c4a451bf65bda58fb2642d1abad3b"),
    (450, 471, "leanprover/lean4:v4.32.0-rc1",
     "b3efe7e8a0863c414a6eb8b1fa19c429f95a81e2",
     "addc160d052569c3ff4acfb94a23e8443ce33c7e", "12321b5724f4ad41d0b60a2005aceb2b865d6c2b"),
    (472, 684, "leanprover/lean4:v4.32.0-rc1",
     "95fdbd69e13b7e6b08d6b2ea72cbb6dd26d0d5f8",
     "d6990f8839bfa9a14cf4efaa768e33aff54e770b", "af4783c9bac74a6263585ad4a336e37e01c7a7cf"),
    (685, 745, "leanprover/lean4:v4.32.0-rc1",
     "40b45a066a39ea5a58a2acf3cf85bf513fc0e241",
     "526789fceccca92a2600c5029001715321af90a5", "9d2e430a17494cbf42ec5d80370bcace88cbc6a2"),
    (746, 775, "leanprover/lean4:v4.32.0-rc1",
     "613038575adbb25fe394846010a0507cfe643053",
     "0cd116dae144aff57af0e35c7e105adec0e4060d", "7fb83c95461ca67d500c9c3d9e6f4647e49eb912"),
    (776, 897, "leanprover/lean4:v4.32.0-rc1",
     "faaff5e5590ad6b6878f66d30a33ded94cd97cf6",
     "acacf9bf346483f038d378415bb7bcb02a4589cb", "52c215ad3f8d3c1bc2caa6af9bec5e4af4f78732"),
    (898, 924, "leanprover/lean4:v4.32.0-rc1",
     "f4e566ca02d995d16c590cdfe4dc051cc80f4624",
     "944129962e0c0c4e8e3c9cf7d00b9e33f8ae9e97", "e289a0905f1b74d4f78143786234dfbec6d16798"),
    (925, 1062, "leanprover/lean4:v4.32.0",
     "81a5d257c8e410db227a6665ed08f64fea08e997",
     "6b8622df38e6cc52533bb73a3e2e77bb86574888", "84923c7d744bd92afae030fcc0c5becdd77da292"),
    (1063, 1129, "leanprover/lean4:v4.32.0",
     "e0824fdc1cf95ea19518210636c74510a36acb05",
     "d81139371df8832bf1fa8e68e4fff92d7a766609", "0f0af98470cc4b014fda8c2b29cb78e4fb3f4b7c"),
    (1130, 1350, "leanprover/lean4:v4.32.0",
     "28313485bc624fcd16dcb162dd2e2c3c813aa8fe",
     "b3464d63d873cca333d169f591d2031cd1c2fdce", "278ce66c349a60e7f96489c26b6d611be277f921"),
    (1351, 1363, "leanprover/lean4:v4.33.0-rc1",
     "79d0395a1825a6264ad5d269e35e60537518955e",
     "a98ea8771fe237edca2339dfcb6d1beb4b9a2320", "b5d0985aa2d40350b5d10eb409c1a7a02e6f7ed1"),
    (1364, 1367, "leanprover/lean4:v4.33.0-rc1",
     "2eb08ab8c9be0180ce78d703513eb713e25ddf53",
     "4618747a4e995686fcd81da039e2fc82127606cf", "111c6ee0bbd2013f18e9c840a146c673525e3636"),
    (1368, 1375, "leanprover/lean4:v4.33.0-rc1",
     "d99d52c36bea862ef9499bfaef386d0bcba9ea48",
     "3a26ae30cade3a1428fce79aa2ec888fe46eb761", "1a6d58475213e55619673a490b66e9b545e2fd07"),
    (1376, 1376, "leanprover/lean4:v4.33.0-rc1",
     "7c8ff804e2608c13c288de9a42c3a5771f124d58",
     "7caffc64eb7398ed48d5f116b44261abc6d57b9c", "7caffc64eb7398ed48d5f116b44261abc6d57b9c"),
    (1377, 1382, "leanprover/lean4:v4.33.0-rc1",
     "d4519b399018129db0a28eda3488eddfed9f73c4",
     "987faf52fdb4f604516b182db576fdedaf877df9", "123bbebb818b5b84d777b09ffea0a394e22d834d"),
    (1383, 1386, "leanprover/lean4:v4.33.0-rc1",
     "d0060d7bbba57d53450b2ebe84d015f5e926793a",
     "be373fcd956bbf1f25c5e5713519865d789e6e90", "54e043e87b338d6d85108068fc0689e241d4cae5"),
    (1387, 1520, "leanprover/lean4:v4.33.0-rc1",
     "c7202db459de001e1f4dcbe9cc244a2be198010f",
     "5cd952648bc879b32bcc0f95e64c1fd8f5e288d3", "aa153fdb48c093cd23415bf97aefb7082f86e085"),
    (1521, 1597, "leanprover/lean4:v4.33.0-rc1",
     "edc39bf7bcc706ba243ae824adaa60fff00416db",
     "e51dd9b19fdd9f4afcf38f09ea787ec83ae7d49a", "01a0f5b2abdb3f9b4616d68b2b209b827ebf42d3"),
    (1598, 1673, "leanprover/lean4:v4.33.0-rc1",
     "30696563acb0596ab44d272bc5dfee96b2e72263",
     "86328ec300dbdecd379c7cf97d27aaa01695e789", "5ff6ce0c8e66574aa23388f09831b2299996f625"),
    (1674, 1815, "leanprover/lean4:v4.33.0-rc1",
     "0f0a217d5d731dad8a22f3f7095634784d30ac14",
     "f522aadb64b228210ad65c3874496280e77f0510", "0560c63d18a70ec1e0994275cf1f93a5f0315c32"),
    (1816, 1910, "leanprover/lean4:v4.33.0-rc1",
     "9c0c555bde5a8277cd36dc4dc6dfe2a5a77a2b11",
     "9afa0a589055ab45857a36177244aca1623bdb20", "249ffa1308e00d2ac4f4f1072ee067881d18db74"),
    (1911, 1920, "leanprover/lean4:v4.33.0-rc1",
     "c0032752b47af314b015a7b411123fa4ac99bbaf",
     "2a2040bfe38e57b1bd304908ac8d640962142ea2", "2e60ddbc2f666712b576cc592daaa4997a2a199e"),
    (1921, 1943, "leanprover/lean4:v4.33.0-rc1",
     "d586c71e87ddf1c4fef06a739cdd3b733fd8b64d",
     "4058bf19b066a045eb774e0f1d63546580fe7324", "3752261a693d758346beb1c004bc967c11545728"),
    (1944, 2096, "leanprover/lean4:v4.33.0-rc2",
     "9fb10993c11c9e7abfa291e86fb499b6e1f4da82",
     "f1d72f954880bb790cf4825443fe16e3d8aa8805", "e574654cbc5550e28d19c3712736ff2be6a755d2"),
    (2097, 2203, "leanprover/lean4:v4.33.0-rc2",
     "7492625a36d9f2fec11042adea9b7eaf9cc22846",
     "21ebbf4e0a77405f75611c5778127b383eb43555", "26089eaea76fe52ce1e4c319e551ec0d603d05da"),
    (2204, 2347, "leanprover/lean4:v4.33.0-rc2",
     "f6dc05e369aa1c3b6a70f416c4b299cf26e9dd38",
     "78d894d611fe8e66aa5bd29a18fd5eeb8132c4ed", "5a778f85832286c96700c52e7a561f339bd8ca5f"),
    (2348, 2401, "leanprover/lean4:v4.33.0-rc2",
     "39122a64484ce32b5fdb6f005e5c2da61773e225",
     "a3d43cf02bb6dc6b7907ac427f1a1be5d3d67771", "afb1aacb3632d3236eee756ea1683290c07270a3"),
    (2402, 2634, "leanprover/lean4:v4.34.0-rc1",
     "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11",
     "3e44c028b2ba2a681c40cbeefb5bded4d637120a", "86cc55d9192fc3f094f293ead6f2e7a153c79d17"),
    (2635, 2719, "leanprover/lean4:v4.34.0-rc1",
     "f5809ef6d5ca171b70db20940625e4f6f36ddee8",
     "41599c661a98d677ea7e9629ff16b72494759e27", "1ecc92cce7e1360dfaf04140ca524ce4a7051ee8"),
    (2720, 2856, "leanprover/lean4:v4.34.0-rc1",
     "f4fd7f7e24a83af258ec9d80deb04648d3428d34",
     "052dec58e5611c2a556cb145f330d541fd12ce89", "de88076c34867b21dd80a7b7232f948dea890c73"),
    (2857, 2981, "leanprover/lean4:v4.34.0-rc1",
     "77cbcbc65f9e26f6ede0a01b24c2cb909e11cc0d",
     "69fd9f9afec87fa107c45b6d9c16972383d12f05", "e28afb19d468aabb12e10f6bc1d226e6cb5e3f97"),
    (2982, 3134, "leanprover/lean4:v4.34.0-rc1",
     "05ae0103f49b1ad1248f6039bbbad43d8aeb52a9",
     "d07f2034e3bff0a6f946d1c590e46e2eca105df9", "ed81293743fa7eb4aaf412bc0cad3050f1d6b8b8"),
    (3135, 3291, "leanprover/lean4:v4.34.0-rc1",
     "5658ee5a7ce168cbe5d8c6bd1c25122c237bf84d",
     "81a74c776bcc5ad72c5f357762b096e81dac4ef7", "c4d7989a116c565aa558fb82c318ad7c651bf2f4"),
    (3292, 3304, "leanprover/lean4:v4.34.0-rc1",
     "ae26804842dd341fb1c52e81d71f1a105ef4ca34",
     "5d5361671ebca14fcf3be2c42c50d9693552f9c7", "f93736047d51931862e138b4c097099c8d1168a6"),
]

# mathlib's release tags over the same window, and the commits they point at.
REAL_TAGS = {
    "v4.31.0-rc1": "d568c8c09630de097a046763c17b9ea99f95f950",
    "v4.31.0-rc2": "d90090f647cae4f4ad4da99c0ac8bab2ca8c34ab",
    "v4.31.0": "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f",
    "v4.32.0-rc1": "360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56",
    "v4.32.0": "81a5d257c8e410db227a6665ed08f64fea08e997",
    "v4.32.1": "520045ab14e26149ee970e2e617ca04b09bde5d6",
    "v4.32.2": "905b95818eb32af7874a58b427f50c1711a5e96c",
    "v4.33.0-rc1": "79d0395a1825a6264ad5d269e35e60537518955e",
    "v4.33.0-rc2": "51e6992efd06126df61a496bebf8f49482a4e129",
    "v4.33.0": "db584cd6d46c92f209a44c0f1c829460d327499d",
    "v4.34.0-rc1": "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11",
}

# The two tags mathlib cut on its `stable` branch. They are not on master, and their
# parent chain reaches master at the v4.32.0 tag commit.
OFF_MASTER = {
    "v4.32.2": "v4.32.1",
    "v4.32.1": "v4.32.0",
}

# The bases the policy must derive, taken from the real history. These are the assertion
# this whole file exists to protect.
EXPECTED_BASES = {
    "v4.31.0-rc2": "d0660b2555379c5b09e6dbd829ace8d147d21f15",
    "v4.32.0-rc1": "b04120e2f4927bde9624602e84833cdc8b5661f9",
    "v4.32.1": "84923c7d744bd92afae030fcc0c5becdd77da292",
    "v4.32.2": "84923c7d744bd92afae030fcc0c5becdd77da292",
    "v4.33.0-rc2": "3752261a693d758346beb1c004bc967c11545728",
    "v4.33.0": "afb1aacb3632d3236eee756ea1683290c07270a3",
}


def segments():
    return [{"first_index": a, "last_index": b, "toolchain": tc, "mathlib_rev": rev,
             "first_sha": first, "last_sha": last}
            for a, b, tc, rev, first, last in REAL_SEGMENTS_RAW]


class FakeUpstream:
    """An offline model of the upstream facts the policy consults.

    Ancestry is modelled the way mathlib's master history actually behaves: the
    toolchain is monotone along it, and a release tag is the FIRST commit carrying its
    own toolchain, so a commit's position is (its toolchain, whether it is the tag).
    The two `stable`-branch tags are off master and reach it through their parents,
    exactly as the real ones do."""

    def __init__(self, tags=None, repo_tags=None, branches=None, verify=None,
                 bump_commits=None, pins=None, shapes=None):
        self.tags = dict(tags or REAL_TAGS)
        self.by_sha = {sha: name for name, sha in self.tags.items()}
        self.repo_tags = dict(repo_tags or {})
        self.branches = dict(branches or {})
        self.verify = dict(verify or {})
        self.pins = dict(pins or {})
        self.shapes = dict(shapes or {})
        self.bump_commits = (set(self.tags) if bump_commits is None else set(bump_commits))
        self.calls = 0
        self._toolchain_of = {}
        for index, (_a, _b, toolchain, rev, _f, _l) in enumerate(REAL_SEGMENTS_RAW):
            self._toolchain_of[rev] = (toolchain, index + 1)

    # ----- ordering along master

    def _order(self, sha):
        name = self.by_sha.get(sha)
        if name is not None:
            return (tt.release_key(name), 0)
        toolchain, index = self._toolchain_of[sha]
        return (tt.release_key(tt.release_of_toolchain(toolchain)), index)

    def _anchor(self, sha):
        """Walk an off-master commit back to the master commit it descends from."""
        name = self.by_sha.get(sha)
        while name in OFF_MASTER:
            name = OFF_MASTER[name]
        return self.tags[name] if name in self.tags else sha

    def on_master(self, sha):
        self.calls += 1
        return self.by_sha.get(sha) not in OFF_MASTER

    def is_ancestor(self, ancestor, descendant):
        self.calls += 1
        if ancestor == descendant:
            return True
        if not self.on_master(descendant):
            descendant = self._anchor(descendant)
            if ancestor == descendant:
                return True
        return self._order(ancestor) < self._order(descendant)

    def is_toolchain_bump_commit(self, sha):
        self.calls += 1
        return sha in {self.tags[n] for n in self.bump_commits if n in self.tags}

    def toolchain_at(self, sha):
        self.calls += 1
        name = self.by_sha.get(sha)
        if name:
            return tt.toolchain_for(name)
        return self._toolchain_of[sha][0]

    def committed_at(self, sha):
        self.calls += 1
        return "2020-01-01T00:00:00Z"

    def release_tags(self):
        self.calls += 1
        return dict(self.tags)

    def tag_target(self, release):
        self.calls += 1
        return self.repo_tags.get(release)

    def branch_head(self, branch):
        # Keyed by the short name, as the real one is: `releases/` is a namespace, and
        # `Upstream.release_branches` strips it when it indexes the matching-refs reply.
        self.calls += 1
        short = branch[len("releases/"):] if branch.startswith("releases/") else branch
        return self.branches.get(short)

    def verify_conclusion(self, sha):
        self.calls += 1
        return self.verify.get(sha)

    def release_branch_shape(self, head):
        self.calls += 1
        return self.shapes.get(head, (True, None))

    def repo_pin_at(self, sha):
        self.calls += 1
        if sha not in self.pins:
            # As the real one does when the API cannot read the commit. Returning something
            # bland here would let a test pass without ever supplying the facts under test.
            raise RuntimeError(f"no pins recorded for {sha}")
        return self.pins[sha]

    def manifest_at(self, sha):
        self.calls += 1
        return MATHLIB_MANIFEST

    def ahead_by(self, base, head):
        self.calls += 1
        return 83 if base == self.tags.get("v4.31.0-rc1") else 1


# A base manifest in Lake's exact layout, trimmed to three packages. The layout, not
# the package count, is what the renderer has to reproduce.
BASE_MANIFEST = '''{"version": "1.2.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover-community/mathlib4",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "1111111111111111111111111111111111111111",
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "2222222222222222222222222222222222222222",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"}],
 "name": "TauCeti",
 "lakeDir": ".lake",
 "fixedToolchain": false}
'''

# mathlib's own manifest at the tag: note `inherited` false on its direct dependency,
# a `version` newer than the base's, and its own root fields, none of which may leak.
MATHLIB_MANIFEST = '''{"version": "1.3.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "3333333333333333333333333333333333333333",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": false,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover/lean4-cli",
   "type": "git",
   "subDir": null,
   "scope": "leanprover",
   "rev": "4444444444444444444444444444444444444444",
   "name": "Cli",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"}],
 "name": "mathlib",
 "lakeDir": ".lake",
 "fixedToolchain": true}
'''

M33 = REAL_TAGS["v4.33.0"]


class RoutedGh:
    """A `core.gh_api` stand-in that answers a fixed set of path shapes and raises on
    anything else, so a new request shape cannot appear unnoticed."""

    def __init__(self, routes):
        self.routes = routes
        self.requests = []

    def __call__(self, path, jq=None, paginate=False):
        self.requests.append(path)
        for prefix, value in self.routes.items():
            if path.startswith(prefix):
                return value
        raise RuntimeError(f"unrouted gh api path: {path}")


@contextlib.contextmanager
def routed(routes):
    fake = RoutedGh(routes)
    original = core.gh_api
    core.gh_api = fake
    try:
        yield fake
    finally:
        core.gh_api = original


# --- version algebra ---------------------------------------------------------

class VersionAlgebra(unittest.TestCase):
    def test_accepts_releases_and_rcs(self):
        self.assertEqual(tt.parse_release("v4.33.0")[:3], (4, 33, 0))
        self.assertEqual(tt.parse_release("v4.33.0-rc2")[3], 2)

    def test_rejects_non_releases(self):
        # `v4.32.0-rc1-patch1` is a mathlib patch of its own tree at an unchanged
        # toolchain, so it names no Lean release and `v4.32.0-rc1` is already taken.
        for name in ("v2024", "v4.32.0-rc1-patch1", "nightly-2026-01-01", "", None):
            self.assertIsNone(tt.parse_release(name), name)

    def test_final_sorts_after_its_own_rcs(self):
        order = ["v4.32.1", "v4.33.0-rc1", "v4.33.0-rc2", "v4.33.0", "v4.34.0-rc1"]
        self.assertEqual(sorted(order, key=tt.release_key), order)
        self.assertTrue(tt.release_lt("v4.33.0-rc2", "v4.33.0"))
        self.assertFalse(tt.release_lt("v4.33.0", "v4.33.0-rc2"))

    def test_toolchain_round_trip(self):
        self.assertEqual(tt.toolchain_for("v4.33.0"), "leanprover/lean4:v4.33.0")
        self.assertEqual(tt.release_of_toolchain("leanprover/lean4:v4.33.0"), "v4.33.0")
        self.assertIsNone(tt.release_of_toolchain("leanprover/lean4-pr-releases:pr-1"))
        self.assertIsNone(tt.release_of_toolchain("leanprover/lean4:nightly-2026-01-01"))


# --- the segment walk --------------------------------------------------------

class SegmentWalk(unittest.TestCase):
    def walk(self, order, changed, pins):
        return tt.segments_from(order, set(changed), lambda sha: pins[sha])

    def test_fills_forward_across_untouched_commits(self):
        pins = {"a": ("tc1", "p1"), "d": ("tc2", "p2")}
        segs = self.walk(list("abcdef"), ["a", "d"], pins)
        self.assertEqual([(s["first_index"], s["last_index"]) for s in segs], [(0, 2), (3, 5)])
        self.assertEqual(segs[0]["last_sha"], "c")
        self.assertEqual(segs[1]["first_sha"], "d")

    def test_a_touch_that_changes_nothing_extends_the_segment(self):
        # A commit can touch lake-manifest.json without moving the pin (a reformat, a
        # revert-and-restore). Splitting there would invent a boundary that no pin move
        # corresponds to, and every later index would shift.
        pins = {"a": ("tc1", "p1"), "c": ("tc1", "p1")}
        segs = self.walk(list("abcd"), ["a", "c"], pins)
        self.assertEqual(len(segs), 1)
        self.assertEqual(segs[0]["last_index"], 3)

    def test_segments_are_contiguous_and_cover_everything(self):
        segs = segments()
        self.assertEqual(segs[0]["first_index"], 0)
        for earlier, later in zip(segs, segs[1:]):
            self.assertEqual(earlier["last_index"] + 1, later["first_index"])

    def test_real_history_is_monotone(self):
        tt.assert_monotone(segments())

    def test_an_unorderable_toolchain_fails_closed(self):
        # The waiver for non-release toolchains was the one case the binary search cannot
        # survive: the fast path's predicate goes false in the middle of the run.
        segs = segments()[:3]
        segs[1] = dict(segs[1], toolchain="leanprover/lean4:nightly-2026-01-01")
        with self.assertRaises(RuntimeError):
            tt.assert_monotone(segs)

    def test_a_backward_toolchain_move_fails_closed(self):
        # Base derivation binary-searches on monotonicity. If main ever moved backward
        # the search would return a silently wrong base, so this must raise.
        segs = segments()[:3]
        segs[2] = dict(segs[2], toolchain="leanprover/lean4:v4.30.0")
        with self.assertRaises(RuntimeError):
            tt.assert_monotone(segs)


# --- base derivation ---------------------------------------------------------

class BaseDerivation(unittest.TestCase):
    def test_every_constructed_release_gets_its_real_base(self):
        up = FakeUpstream()
        for release, expected in EXPECTED_BASES.items():
            with self.subTest(release=release):
                base, _rule = tt.resolve_base(segments(), release, REAL_TAGS[release], up)
                self.assertIsNotNone(base, f"{release} derived no base")
                self.assertEqual(base["last_sha"], expected)

    def test_the_naive_toolchain_rule_gets_the_patch_releases_wrong(self):
        # Documents why the exact-pin clause and the off-master walk exist. "The last
        # segment whose toolchain is older than X" lands well past v4.32.1's real base,
        # because v4.32.1 branches off the v4.32.0 TAG, not off the end of that era.
        segs = segments()
        naive = [s for s in segs
                 if tt.release_lt(tt.release_of_toolchain(s["toolchain"]), "v4.32.1")][-1]
        self.assertNotEqual(naive["last_sha"], EXPECTED_BASES["v4.32.1"])

    def test_the_fast_path_and_a_real_ancestry_search_agree(self):
        # The fast path rests on mathlib's habit of tagging the toolchain-bump commit.
        # Turning the habit off must not change any answer, only the cost.
        for release, expected in EXPECTED_BASES.items():
            with self.subTest(release=release):
                slow = FakeUpstream(bump_commits=set())
                base, rule = tt.resolve_base(segments(), release, REAL_TAGS[release], slow)
                self.assertEqual(rule, "ancestry-search")
                self.assertEqual(base["last_sha"], expected)

    def test_the_fast_path_is_cheaper(self):
        fast, slow = FakeUpstream(), FakeUpstream(bump_commits=set())
        tt.resolve_base(segments(), "v4.33.0", REAL_TAGS["v4.33.0"], fast)
        tt.resolve_base(segments(), "v4.33.0", REAL_TAGS["v4.33.0"], slow)
        self.assertLess(fast.calls, slow.calls)

    def test_a_wrong_fast_path_is_caught_and_corrected(self):
        # If mathlib ever reverts to tagging a commit that is NOT the toolchain bump,
        # as it did for v4.24.0, the fast path's premise is false. The verification
        # query must notice and fall back rather than return a wrong base.
        class Liar(FakeUpstream):
            def is_toolchain_bump_commit(self, sha):
                return True  # claims the habit holds when it does not

            def _order(self, sha):
                # v4.33.0's tag now sits at the END of its own era, so every pin the
                # fast path would accept on toolchain grounds is still an ancestor,
                # except the era's own, which it wrongly rejects.
                order = super()._order(sha)
                if self.by_sha.get(sha) == "v4.33.0":
                    return (order[0], 99)
                return order

        up = Liar()
        base, _rule = tt.resolve_base(segments(), "v4.33.0", REAL_TAGS["v4.33.0"], up)
        self.assertTrue(up.is_ancestor(base["mathlib_rev"], REAL_TAGS["v4.33.0"]))

    def test_no_base_when_the_repository_starts_after_the_tag(self):
        # v4.31.0-rc1's tag predates the first commit, which already pins past it.
        base, _rule = tt.resolve_base(segments(), "v4.31.0-rc1", REAL_TAGS["v4.31.0-rc1"],
                                      FakeUpstream())
        self.assertIsNone(base)


# --- classification ----------------------------------------------------------

class Classification(unittest.TestCase):
    def row(self, release, up=None):
        up = up or FakeUpstream()
        return tt.classify(release, REAL_TAGS[release], segments(), up)

    def test_the_four_exact_runs_are_ready_at_the_first_commit_of_the_run(self):
        expected = {
            "v4.31.0": "d2da4153396c7a2d57f3d068d194fb91468cfa40",
            "v4.32.0": "6b8622df38e6cc52533bb73a3e2e77bb86574888",
            "v4.33.0-rc1": "a98ea8771fe237edca2339dfcb6d1beb4b9a2320",
            "v4.34.0-rc1": "3e44c028b2ba2a681c40cbeefb5bded4d637120a",
        }
        for release, sha in expected.items():
            with self.subTest(release=release):
                row = self.row(release)
                self.assertEqual(row["status"], "ready")
                self.assertTrue(row["exact"])
                self.assertEqual(row["target_sha"], sha)

    def test_the_target_does_not_move_as_main_grows(self):
        # The reason RUN_TAG_POLICY is "first". The v4.34.0-rc1 run is at the tip, so
        # main keeps appending commits to it; under "last" the tag would want to move
        # on every one of them and would never be idempotent.
        before = self.row("v4.34.0-rc1")["target_sha"]
        grown = segments()
        grown[-1] = dict(grown[-1], last_index=grown[-1]["last_index"] + 500,
                         last_sha="f" * 40)
        after = tt.classify("v4.34.0-rc1", REAL_TAGS["v4.34.0-rc1"], grown, FakeUpstream())
        self.assertEqual(before, after["target_sha"])

    def test_the_policy_constant_is_what_selects_the_commit(self):
        # Keeps RUN_TAG_POLICY load-bearing. It was documentation that nothing read
        # once, which is how a stated policy and an actual one drift apart.
        original = tt.RUN_TAG_POLICY
        try:
            first = self.row("v4.31.0")["target_sha"]
            tt.RUN_TAG_POLICY = "last"
            last = self.row("v4.31.0")["target_sha"]
        finally:
            tt.RUN_TAG_POLICY = original
        self.assertNotEqual(first, last)
        self.assertEqual(first, "d2da4153396c7a2d57f3d068d194fb91468cfa40")

    def test_constructed_releases_need_a_branch_and_name_their_base(self):
        for release, base in EXPECTED_BASES.items():
            with self.subTest(release=release):
                row = self.row(release)
                self.assertEqual(row["status"], "needs-branch")
                self.assertEqual(row["base_sha"], base)
                self.assertIsNone(row["target_sha"])

    def test_an_existing_release_branch_becomes_the_target(self):
        head = "a" * 40
        up = FakeUpstream(branches={"v4.33.0": head},
                          pins={head: ("leanprover/lean4:v4.33.0", REAL_TAGS["v4.33.0"])})
        row = self.row("v4.33.0", up)
        self.assertEqual(row["status"], "branch-ready")
        self.assertEqual(row["target_sha"], head)
        self.assertEqual(row["target_kind"], "release-branch")

    def test_a_release_branch_carrying_more_than_the_pins_is_not_a_target(self):
        # Right pins, wrong shape. A commit that also changes source would otherwise be
        # nominated as a permanent tag target; the release workflow would refuse it later,
        # but the audit should not be pointing at it in the meantime.
        head = "a" * 40
        up = FakeUpstream(branches={"v4.33.0": head},
                          pins={head: ("leanprover/lean4:v4.33.0", REAL_TAGS["v4.33.0"])},
                          shapes={head: (False, "changes TauCeti/Foo.lean, which is outside "
                                                "the two Lake pins")})
        row = self.row("v4.33.0", up)
        self.assertEqual(row["status"], "blocked")
        self.assertIn("outside the two Lake pins", row["reason"])

    def test_an_unreadable_release_branch_is_not_called_wrong(self):
        # A blinking API is not a verdict, and must not produce advice to re-cut a branch
        # that may be perfectly correct.
        head = "a" * 40
        up = FakeUpstream(branches={"v4.33.0": head})   # no pins recorded: repo_pin_at raises
        row = self.row("v4.33.0", up)
        self.assertEqual(row["status"], "blocked")
        self.assertIn("could not be read", row["reason"])
        self.assertNotIn("re-cut", row["reason"])

    def test_a_tag_is_not_judged_against_a_branch_that_has_since_moved(self):
        # A permanent tag compared with a mutable branch head would start reading as a
        # mismatch the moment someone re-cut the branch onto another exact-pin commit.
        tagged, moved = "b" * 40, "c" * 40
        pins = {sha: ("leanprover/lean4:v4.33.0", REAL_TAGS["v4.33.0"])
                for sha in (tagged, moved)}
        up = FakeUpstream(branches={"v4.33.0": moved}, pins=pins,
                          repo_tags={"v4.33.0": tagged})
        self.assertEqual(self.row("v4.33.0", up)["status"], "tagged")

    def test_a_release_branch_pointing_anywhere_is_not_a_target(self):
        # Creating `releases/vX` at an arbitrary commit must not make that commit the
        # permanent tag target. The release workflow's own checker would refuse it later,
        # but the audit should not be naming it in the meantime.
        head = "a" * 40
        up = FakeUpstream(branches={"v4.33.0": head},
                          pins={head: ("leanprover/lean4:v4.33.0", "9" * 40)})
        row = self.row("v4.33.0", up)
        self.assertEqual(row["status"], "blocked")
        self.assertIn("re-cut it", row["reason"])

    def test_the_inexact_rung_is_used_only_when_no_base_exists(self):
        row = self.row("v4.31.0-rc1")
        self.assertEqual(row["status"], "ready")
        self.assertFalse(row["exact"])
        self.assertEqual(row["target_sha"], REAL_SEGMENTS_RAW[0][4])

    def test_releases_predating_the_repository_are_out_of_scope_and_free(self):
        up = FakeUpstream(tags=dict(REAL_TAGS, **{"v4.20.0": "b" * 40}))
        row = tt.classify("v4.20.0", "b" * 40, segments(), up)
        self.assertEqual(row["status"], "out-of-scope")
        self.assertEqual(up.calls, 0, "an out-of-scope release must cost no API calls")

    def test_a_green_release_build_makes_a_target_verified(self):
        sha = "3e44c028b2ba2a681c40cbeefb5bded4d637120a"
        row = self.row("v4.34.0-rc1", FakeUpstream(verify={sha: "success"}))
        self.assertEqual(row["status"], "verified")

    def test_a_red_release_build_blocks_without_claiming_it_cannot_be_built(self):
        sha = "3e44c028b2ba2a681c40cbeefb5bded4d637120a"
        row = self.row("v4.34.0-rc1", FakeUpstream(verify={sha: "failure"}))
        self.assertEqual(row["status"], "blocked")
        self.assertIn("not the same as", row["reason"])

    def test_an_existing_tag_is_judged_by_its_own_pins(self):
        sha = "3e44c028b2ba2a681c40cbeefb5bded4d637120a"
        up = FakeUpstream(repo_tags={"v4.34.0-rc1": sha},
                          pins={sha: ("leanprover/lean4:v4.34.0-rc1",
                                      REAL_TAGS["v4.34.0-rc1"])})
        self.assertEqual(self.row("v4.34.0-rc1", up)["status"], "tagged")

    def test_a_tag_on_a_deleted_release_branch_stays_tagged(self):
        # Judging a tag by re-deriving today's target would call this a mismatch the
        # moment the release branch is deleted, which is a harmless piece of tidying.
        sha = "c" * 40
        up = FakeUpstream(repo_tags={"v4.33.0": sha},
                          pins={sha: ("leanprover/lean4:v4.33.0", REAL_TAGS["v4.33.0"])})
        self.assertEqual(self.row("v4.33.0", up)["status"], "tagged")

    def test_an_inexact_tag_is_accepted_when_its_pin_descends_from_the_release(self):
        sha = REAL_SEGMENTS_RAW[0][4]
        up = FakeUpstream(repo_tags={"v4.31.0-rc1": sha},
                          pins={sha: ("leanprover/lean4:v4.31.0-rc1",
                                      REAL_SEGMENTS_RAW[0][3])})
        row = self.row("v4.31.0-rc1", up)
        self.assertEqual(row["status"], "tagged")
        self.assertFalse(row["exact"])

    def test_a_tag_on_the_wrong_commit_of_an_exact_run_is_blocked(self):
        # The policy word is "first". A tag placed on a later commit of the same run, or on
        # main's tip, has the right toolchain and a pin at or after the release, so a check
        # that asked only those questions would bless a permanent tag on the wrong commit.
        wrong = REAL_SEGMENTS_RAW[-1][5]
        up = FakeUpstream(repo_tags={"v4.34.0-rc1": wrong},
                          pins={wrong: ("leanprover/lean4:v4.34.0-rc1",
                                        REAL_SEGMENTS_RAW[-1][3])})
        row = self.row("v4.34.0-rc1", up)
        self.assertEqual(row["status"], "blocked")
        self.assertIn("policy names", row["reason"])

    def test_a_tag_on_the_wrong_toolchain_is_blocked_and_never_moved(self):
        sha = "d" * 40
        up = FakeUpstream(repo_tags={"v4.33.0": sha},
                          pins={sha: ("leanprover/lean4:v4.34.0-rc1", REAL_TAGS["v4.33.0"])})
        row = self.row("v4.33.0", up)
        self.assertEqual(row["status"], "blocked")
        recipe = tt.recipe_for(row) or ""
        for forbidden in ("--force", "tag -d", " -f "):
            self.assertNotIn(forbidden, recipe)


# --- the release commit's two files ------------------------------------------

class ManifestLayout(unittest.TestCase):
    def test_round_trips_this_repository_s_own_manifest_byte_for_byte(self):
        # The renderer reproduces Lake's layout from the bytes rather than from a
        # guess, so if Lake ever changes it this fails instead of the tool emitting a
        # whole-file diff on every release commit.
        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        with open(os.path.join(root, "lake-manifest.json")) as handle:
            text = handle.read()
        self.assertEqual(tt.render_manifest(tt.parse_manifest(text)), text)

    def test_round_trips_the_fixtures(self):
        for text in (BASE_MANIFEST, MATHLIB_MANIFEST):
            self.assertEqual(tt.render_manifest(tt.parse_manifest(text)), text)


class DeriveManifest(unittest.TestCase):
    def derived(self):
        return tt.parse_manifest(tt.derive_manifest(BASE_MANIFEST, MATHLIB_MANIFEST, M33))

    def test_mathlib_comes_first_and_only_its_rev_changes(self):
        pkg = self.derived()["packages"][0]
        base = tt.parse_manifest(BASE_MANIFEST)["packages"][0]
        self.assertEqual(pkg["name"], "mathlib")
        self.assertEqual(pkg["rev"], M33)
        for key in ("url", "scope", "configFile", "inputRev", "inherited", "subDir"):
            self.assertEqual(pkg[key], base[key], key)

    def test_dependencies_are_mathlib_s_own_normalised_to_inherited(self):
        out = self.derived()
        deps = {p["name"]: p for p in out["packages"] if p["name"] != "mathlib"}
        upstream = {p["name"]: p for p in tt.parse_manifest(MATHLIB_MANIFEST)["packages"]}
        self.assertEqual(set(deps), set(upstream))
        for name, pkg in deps.items():
            self.assertTrue(pkg["inherited"], f"{name} is transitive from here")
            for key in ("type", "url", "rev", "inputRev", "scope", "configFile"):
                self.assertEqual(pkg[key], upstream[name][key], f"{name}.{key}")
        self.assertEqual(list(deps["batteries"]), list(upstream["batteries"]),
                         "normalising `inherited` must not reorder the keys")

    def test_root_fields_are_ours_except_the_manifest_format_version(self):
        out = self.derived()
        base = tt.parse_manifest(BASE_MANIFEST)
        self.assertEqual(out["name"], "TauCeti")
        self.assertEqual(out["lakeDir"], base["lakeDir"])
        self.assertEqual(out["fixedToolchain"], base["fixedToolchain"])
        self.assertEqual(list(out), list(base), "root key order is preserved")
        # `version` is Lake's manifest-format version, written by the Lake that ships
        # with the target toolchain, so mathlib's copy at the tag is the current one.
        self.assertEqual(out["version"], "1.3.0")

    def test_it_satisfies_what_bump_guard_compares(self):
        # check-bump.sh step 3 compares (type, normalised url, rev, inputRev) for every
        # package except mathlib against mathlib's own manifest. Re-implemented here so
        # the constructor cannot drift away from the guard that has to accept it.
        def norm(url):
            url = (url or "").rstrip("/")
            return url[:-4] if url.endswith(".git") else url

        def tup(pkg):
            return (pkg.get("type"), norm(pkg.get("url")), pkg.get("rev"), pkg.get("inputRev"))

        ours = {p["name"]: p for p in self.derived()["packages"] if p["name"] != "mathlib"}
        theirs = {p["name"]: p for p in tt.parse_manifest(MATHLIB_MANIFEST)["packages"]}
        self.assertEqual(set(ours), set(theirs))
        for name in theirs:
            self.assertEqual(tup(ours[name]), tup(theirs[name]), name)

    def test_it_refuses_a_base_whose_nomination_is_not_master(self):
        base = BASE_MANIFEST.replace('"inputRev": "master"', '"inputRev": "v4.33.0"', 1)
        with self.assertRaises(ValueError):
            tt.derive_manifest(base, MATHLIB_MANIFEST, M33)

    def test_it_refuses_a_non_sha_rev_and_a_non_git_dependency(self):
        with self.assertRaises(ValueError):
            tt.derive_manifest(BASE_MANIFEST, MATHLIB_MANIFEST, "master")
        upstream = MATHLIB_MANIFEST.replace('"type": "git"', '"type": "path"', 1)
        with self.assertRaises(ValueError):
            tt.derive_manifest(BASE_MANIFEST, upstream, M33)

    def test_it_refuses_an_upstream_manifest_that_contains_mathlib(self):
        upstream = MATHLIB_MANIFEST.replace('"name": "batteries"', '"name": "mathlib"', 1)
        with self.assertRaises(ValueError):
            tt.derive_manifest(BASE_MANIFEST, upstream, M33)


class DeriveToolchain(unittest.TestCase):
    def test_content_and_trailing_newline_convention(self):
        # This repository's lean-toolchain has no trailing newline and mathlib's does.
        # Matching mathlib would add a whitespace-only diff for nothing; bump-guard
        # strips whitespace when it compares, so both are valid and the minimal diff wins.
        self.assertEqual(tt.derive_toolchain("leanprover/lean4:v4.32.0", "v4.33.0"),
                         "leanprover/lean4:v4.33.0")
        self.assertEqual(tt.derive_toolchain("leanprover/lean4:v4.32.0\n", "v4.33.0"),
                         "leanprover/lean4:v4.33.0\n")


class WriteReleaseFiles(unittest.TestCase):
    def test_writes_exactly_two_files_with_the_derived_content(self):
        up = FakeUpstream()
        base = EXPECTED_BASES["v4.33.0"]
        with tempfile.TemporaryDirectory() as directory:
            original = tt.blob_at
            tt.blob_at = lambda sha, path: (BASE_MANIFEST if path.endswith(".json")
                                            else "leanprover/lean4:v4.33.0-rc2")
            try:
                written = tt.write_release_files(directory, "v4.33.0", M33, base, up)
            finally:
                tt.blob_at = original
            self.assertEqual(sorted(os.listdir(directory)),
                             ["lake-manifest.json", "lean-toolchain"])
            self.assertEqual(len(written), 2)
            with open(os.path.join(directory, "lean-toolchain")) as handle:
                self.assertEqual(handle.read(), "leanprover/lean4:v4.33.0")
            with open(os.path.join(directory, "lake-manifest.json")) as handle:
                manifest = tt.parse_manifest(handle.read())
            self.assertEqual(manifest["packages"][0]["rev"], M33)

    def test_it_refuses_a_tag_that_does_not_name_the_toolchain_it_claims(self):
        class Mislabelled(FakeUpstream):
            def toolchain_at(self, sha):
                return "leanprover/lean4:v4.32.0"

        with tempfile.TemporaryDirectory() as directory:
            original = tt.blob_at
            tt.blob_at = lambda sha, path: (BASE_MANIFEST if path.endswith(".json")
                                            else "leanprover/lean4:v4.33.0-rc2")
            try:
                with self.assertRaises(RuntimeError):
                    tt.write_release_files(directory, "v4.33.0", M33, "base", Mislabelled())
            finally:
                tt.blob_at = original


# --- tag metadata ------------------------------------------------------------

class TagMetadata(unittest.TestCase):
    def row(self, release="v4.33.0", exact=True, distance=None):
        return {"release": release, "toolchain": tt.toolchain_for(release),
                "mathlib_rev": REAL_TAGS[release], "target_sha": "e" * 40,
                "target_kind": "release-branch", "exact": exact, "distance": distance}

    def test_round_trips_through_the_marker(self):
        meta = tt.parse_tag_message(tt.tag_message(self.row()))
        self.assertEqual(meta["release"], "v4.33.0")
        self.assertEqual(meta["mathlib_rev"], REAL_TAGS["v4.33.0"])
        self.assertTrue(meta["exact"])

    def test_an_inexact_tag_records_its_distance_in_both_forms(self):
        message = tt.tag_message(self.row("v4.31.0-rc1", exact=False, distance=83))
        self.assertIn("no, 83 mathlib commits past the tag", message)
        self.assertEqual(tt.parse_tag_message(message)["distance"], 83)

    def test_a_marker_quoted_earlier_in_the_body_is_not_the_marker(self):
        # Anchored to the end, as stuck_alerts does, so a message that discusses a
        # marker cannot be read as carrying one.
        real = tt.tag_message(self.row())
        decoy = '<!--tauceti-toolchain-tag:v1 {"release": "v9.9.9"}-->\n\n' + real
        self.assertEqual(tt.parse_tag_message(decoy)["release"], "v4.33.0")

    def test_a_malformed_marker_is_no_marker(self):
        self.assertIsNone(tt.parse_tag_message("nothing here"))
        self.assertIsNone(tt.parse_tag_message("<!--tauceti-toolchain-tag:v1 {not json}-->"))


# --- the stepping stone ------------------------------------------------------

class SteppingStone(unittest.TestCase):
    def segments_pinned_at(self, release, rev):
        segs = segments()
        segs[-1] = dict(segs[-1], toolchain=tt.toolchain_for(release), mathlib_rev=rev)
        return segs

    def test_it_names_the_release_the_bump_would_hop_over(self):
        # main sits on v4.33.0-rc2 while the bump target has reached v4.34.0-rc1, so
        # the next stone is v4.33.0: the release in between that main never pinned.
        segs = self.segments_pinned_at("v4.33.0-rc2", REAL_TAGS["v4.33.0-rc2"])
        up = FakeUpstream()
        self.assertEqual(tt.next_stepping_stone(segs, up, REAL_TAGS["v4.34.0-rc1"]),
                         REAL_TAGS["v4.33.0"])

    def test_it_names_the_smallest_uncrossed_release_first(self):
        segs = self.segments_pinned_at("v4.33.0-rc1", REAL_TAGS["v4.33.0-rc1"])
        up = FakeUpstream()
        self.assertEqual(tt.next_stepping_stone(segs, up, REAL_TAGS["v4.34.0-rc1"]),
                         REAL_TAGS["v4.33.0-rc2"])

    def test_nothing_to_do_when_the_target_is_where_main_already_is(self):
        segs = self.segments_pinned_at("v4.34.0-rc1", REAL_TAGS["v4.34.0-rc1"])
        self.assertIsNone(tt.next_stepping_stone(segs, FakeUpstream(),
                                                 REAL_TAGS["v4.34.0-rc1"]))

    def test_it_never_proposes_a_stable_branch_patch_release(self):
        # bump-guard requires the new rev to be on the nominated branch, so a stone
        # pinning v4.32.1 could never merge. Those are backfill-only by construction.
        segs = self.segments_pinned_at("v4.32.0", REAL_TAGS["v4.32.0"])
        stone = tt.next_stepping_stone(segs, FakeUpstream(), REAL_TAGS["v4.33.0"])
        self.assertNotIn(stone, (REAL_TAGS["v4.32.1"], REAL_TAGS["v4.32.2"]))
        self.assertEqual(stone, REAL_TAGS["v4.33.0-rc1"])


# --- the report --------------------------------------------------------------

class Report(unittest.TestCase):
    def rows(self):
        return tt.audit(segments(), FakeUpstream())

    def test_the_policy_is_part_of_the_output(self):
        text = tt.render_audit(self.rows())
        for phrase in ("Tau Ceti toolchain tags", "exact", "inexact",
                       "Tags are NEVER moved", "release-tag.yml"):
            self.assertIn(phrase, text)

    def test_out_of_scope_releases_are_collapsed_unless_asked_for(self):
        # mathlib carries about ninety tags that predate this repository. Reading past
        # them to reach the actionable rows is the whole cost of the report.
        old = ["v4.20.0", "v4.21.0"]
        up = FakeUpstream(tags=dict(REAL_TAGS, **{name: "b" * 40 for name in old}))
        rows = tt.audit(segments(), up)

        def row_names(text):
            return {line.split()[0] for line in text.splitlines() if line.startswith("v4.")}

        collapsed = tt.render_table(rows)
        self.assertFalse(row_names(collapsed) & set(old))
        self.assertIn("predate this repository", collapsed)
        self.assertTrue(set(old) <= row_names(tt.render_table(rows, show_all=True)))

    def test_every_actionable_release_gets_an_actionable_recipe(self):
        for row in tt.actionable(self.rows()):
            with self.subTest(release=row["release"]):
                recipe = tt.recipe_for(row)
                self.assertTrue(recipe, f"{row['release']} has no recipe")
                if row["status"] == "needs-branch":
                    self.assertIn(row["base_sha"], recipe)
                    self.assertIn(row["branch"], recipe)
                    self.assertIn("--write", recipe)
                elif row["status"] != "blocked":
                    self.assertIn(row["target_sha"], recipe)
                    self.assertIn("gh workflow run release-tag.yml", recipe)

    def test_no_recipe_ever_moves_or_deletes_a_tag(self):
        # `gh workflow run -f field=value` is fine; what must never appear is anything
        # that could move or remove a published tag.
        text = tt.render_audit(self.rows())
        for forbidden in ("--force", "tag -f", "tag -d", "push --delete", "update-ref -d"):
            self.assertNotIn(forbidden, text)

    def test_the_json_worklist_is_one_terminal_status_per_release(self):
        rows = json.loads(tt.rows_to_json(self.rows()))
        self.assertEqual(len(rows), len({r["release"] for r in rows}))
        for row in rows:
            self.assertIn(row["status"], tt.STATUSES)
            for key in ("release", "toolchain", "mathlib_rev", "status", "exact"):
                self.assertIn(key, row)

    def test_the_audit_reaches_the_network_only_through_Upstream(self):
        # `_distance` once called `gh api` directly, so every audit in this file was
        # quietly doing real network round trips. Anything that bypasses `Upstream` is
        # both untestable offline and invisible to the request budget.
        with routed({}) as fake:
            tt.audit(segments(), FakeUpstream())
            self.assertEqual(fake.requests, [])

    def test_the_report_reproduces_the_eleven_in_scope_releases(self):
        rows = [r for r in self.rows() if r["status"] != "out-of-scope"]
        self.assertEqual(len(rows), 11)
        counts = {}
        for row in rows:
            counts[row["status"]] = counts.get(row["status"], 0) + 1
        self.assertEqual(counts, {"ready": 5, "needs-branch": 6})
        self.assertEqual([r["release"] for r in rows if not r["exact"]], ["v4.31.0-rc1"])


# --- the request budget and the cache ----------------------------------------

class RefNamespaces(unittest.TestCase):
    """The query prefix and the ref namespace are different things.

    Querying `tags/v` and then stripping `refs/tags/v` keyed every tag without its leading
    `v`, so every lookup missed and every existing tag was reported absent for ever. The
    request-budget fake returned an empty tag namespace, which is precisely why no test
    noticed."""

    ROUTES = {
        "repos/TauCetiProject/TauCeti/git/matching-refs/tags/v":
            "refs/tags/v4.33.0\tdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef\tcommit\n"
            "refs/tags/v4.34.0-rc1\tcafebabecafebabecafebabecafebabecafebabe\ttag\n",
        "repos/TauCetiProject/TauCeti/git/matching-refs/heads/releases/":
            "refs/heads/releases/v4.33.0\tfeedfacefeedfacefeedfacefeedfacefeedface\tcommit\n",
        "repos/TauCetiProject/TauCeti/git/tags/":
            "1111111111111111111111111111111111111111",
    }

    def test_a_lightweight_tag_is_found_under_its_own_name(self):
        with routed(self.ROUTES):
            up = tt.Upstream(cache=tt.Cache(path=os.devnull))
            self.assertEqual(up.tag_target("v4.33.0"),
                             "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef")

    def test_an_annotated_tag_is_peeled(self):
        with routed(self.ROUTES):
            up = tt.Upstream(cache=tt.Cache(path=os.devnull))
            self.assertEqual(up.tag_target("v4.34.0-rc1"), "1" * 40)

    def test_an_absent_tag_is_absent(self):
        with routed(self.ROUTES):
            up = tt.Upstream(cache=tt.Cache(path=os.devnull))
            self.assertIsNone(up.tag_target("v4.31.0"))

    def test_a_release_branch_is_found_under_its_short_name(self):
        with routed(self.ROUTES):
            up = tt.Upstream(cache=tt.Cache(path=os.devnull))
            self.assertEqual(up.branch_head("releases/v4.33.0"),
                             "feedfacefeedfacefeedfacefeedfacefeedface")


class RequestBudget(unittest.TestCase):
    """The perf design, written as a test: reading a pin per commit rather than per
    segment, or querying a tag per release rather than a namespace at a time, is the
    regression that turns a seconds-long report into a minutes-long one."""

    ROUTES = {
        "repos/leanprover-community/mathlib4/git/matching-refs/tags/v":
            "refs/tags/v4.33.0\t" + REAL_TAGS["v4.33.0"] + "\tcommit\n",
        "repos/TauCetiProject/TauCeti/git/matching-refs/tags/v": "",
        "repos/TauCetiProject/TauCeti/git/matching-refs/heads/releases/": "",
        "repos/TauCetiProject/TauCeti/actions/workflows/": "",
        "repos/leanprover-community/mathlib4/compare/": "ahead",
        "repos/leanprover-community/mathlib4/git/commits/":
            REAL_TAGS["v4.33.0-rc2"],
        "repos/leanprover-community/mathlib4/contents/lean-toolchain":
            "bGVhbnByb3Zlci9sZWFuNDp2NC4zMy4wCg==",
    }

    def test_a_whole_audit_stays_inside_its_budget(self):
        with routed(self.ROUTES) as fake:
            up = tt.Upstream(cache=tt.Cache(path=os.devnull))
            tt.audit(segments(), up)
            self.assertLess(len(fake.requests), 60,
                            f"{len(fake.requests)} requests: something is querying per "
                            "commit or per release where it should batch")

    def test_the_tag_and_branch_namespaces_are_each_one_request(self):
        with routed(self.ROUTES) as fake:
            up = tt.Upstream(cache=tt.Cache(path=os.devnull))
            tt.audit(segments(), up)
            for prefix in ("repos/TauCetiProject/TauCeti/git/matching-refs/tags/v",
                           "repos/TauCetiProject/TauCeti/git/matching-refs/heads/releases/"):
                hits = [p for p in fake.requests if p.startswith(prefix)]
                self.assertEqual(len(hits), 1, prefix)

    def test_an_unrecognised_request_shape_is_a_failure(self):
        with routed({}) as fake:
            with self.assertRaises(RuntimeError):
                tt.Upstream(cache=tt.Cache(path=os.devnull)).release_tags()
            self.assertTrue(fake.requests)


class CacheBehaviour(unittest.TestCase):
    def test_round_trip_and_flush(self):
        with tempfile.TemporaryDirectory() as directory:
            path = os.path.join(directory, "sub", "cache.json")
            cache = tt.Cache(path=path)
            cache.put(("toolchain", "abc"), "leanprover/lean4:v4.33.0")
            cache.flush()
            self.assertEqual(tt.Cache(path=path).get(("toolchain", "abc")),
                             "leanprover/lean4:v4.33.0")

    def test_a_corrupt_or_unwritable_cache_is_ignored_rather_than_fatal(self):
        with tempfile.TemporaryDirectory() as directory:
            path = os.path.join(directory, "cache.json")
            with open(path, "w") as handle:
                handle.write("{not json")
            cache = tt.Cache(path=path)
            self.assertIsNone(cache.get(("toolchain", "abc")))
            cache.put(("toolchain", "abc"), "x")
            cache.flush()  # must not raise

    def test_immutable_facts_are_cached_and_a_moving_ref_is_not(self):
        routes = dict(RequestBudget.ROUTES)
        with routed(routes) as fake:
            up = tt.Upstream(cache=tt.Cache(path=os.devnull))
            up.toolchain_at("abc")
            up.toolchain_at("abc")
            contents = [p for p in fake.requests if "contents/lean-toolchain" in p]
            self.assertEqual(len(contents), 1, "an immutable blob was fetched twice")
            up.compare("abc", "master")
            up.compare("abc", "master")
            compares = [p for p in fake.requests if "/compare/" in p]
            self.assertEqual(len(compares), 2, "a moving ref must not be cached")


# --- Zulip -------------------------------------------------------------------

class FakeZulip:
    def __init__(self, messages=None, bot_id=7):
        self.messages = list(messages or [])
        self.bot_id = bot_id
        self.sent = []
        self.updated = []

    def my_user_id(self):
        return self.bot_id

    def get_messages(self, narrow):
        return self.messages

    def send_message(self, content):
        self.sent.append(content)
        return len(self.sent)

    def update_message(self, message_id, content):
        self.updated.append((message_id, content))


class Alerts(unittest.TestCase):
    def alert(self, key="needs-branch/v4.33.0", title="t", body="b"):
        return {"key": key, "title": title, "body": body}

    def msg(self, alert, ident=1, sender=7, resolved=False):
        content = (tt.resolved_content(alert["key"], alert["title"]) if resolved
                   else tt.alert_content(alert))
        return {"id": ident, "sender_id": sender, "content": content}

    def test_a_new_alert_is_posted(self):
        z = FakeZulip()
        tt.reconcile(z, [self.alert()], set(), dry_run=False)
        self.assertEqual(len(z.sent), 1)

    def test_an_unchanged_alert_is_left_alone(self):
        alert = self.alert()
        z = FakeZulip([self.msg(alert)])
        tt.reconcile(z, [alert], set(), dry_run=False)
        self.assertEqual((z.sent, z.updated), ([], []))

    def test_a_changed_alert_is_edited(self):
        alert = self.alert()
        z = FakeZulip([self.msg(alert)])
        tt.reconcile(z, [self.alert(body="different")], set(), dry_run=False)
        self.assertEqual(len(z.updated), 1)
        self.assertEqual(z.sent, [])

    def test_a_cleared_alert_is_edited_to_the_resolved_form(self):
        alert = self.alert()
        z = FakeZulip([self.msg(alert)])
        tt.reconcile(z, [], set(), dry_run=False)
        self.assertEqual(len(z.updated), 1)
        self.assertTrue(z.updated[0][1].lstrip().startswith(tt.GREEN))

    def test_a_recurrence_posts_afresh_rather_than_editing_a_buried_tick(self):
        alert = self.alert()
        z = FakeZulip([self.msg(alert, resolved=True)])
        tt.reconcile(z, [alert], set(), dry_run=False)
        self.assertEqual(len(z.sent), 1)
        self.assertEqual(z.updated, [])

    def test_a_failed_classification_resolves_nothing(self):
        # Fail closed: a run that could not work out the state must never report that
        # an outstanding release is now fine.
        alert = self.alert()
        z = FakeZulip([self.msg(alert)])
        tt.reconcile(z, [], {"needs-branch"}, dry_run=False)
        self.assertEqual(z.updated, [])

    def test_dry_run_touches_nothing(self):
        z = FakeZulip()
        tt.reconcile(z, [self.alert()], set(), dry_run=True)
        self.assertEqual((z.sent, z.updated), ([], []))

    def test_the_alert_key_survives_a_change_of_status(self):
        # needs-branch -> branch-ready is progress, not resolution. Keying on the status
        # retired the old key, and the reconciler then edited the original message to a
        # green tick for a release that was still untagged.
        rows = tt.audit(segments(), FakeUpstream())
        before = {a["key"] for a in tt.alerts_from(rows, FakeUpstream())}
        moved = [dict(r, status="branch-ready", target_sha="a" * 40)
                 if r["status"] == "needs-branch" else r for r in rows]
        after = {a["key"] for a in tt.alerts_from(moved, FakeUpstream())}
        self.assertEqual(before, after)

    def test_a_built_but_untagged_release_still_alerts(self):
        # `verified` is the state where the expensive part is done and only the one cheap
        # irreversible step is missing. Silencing it let a release sit built and untagged
        # for ever with the workflow green.
        rows = [dict(r, status="verified") for r in tt.audit(segments(), FakeUpstream())
                if r["status"] == "ready"][:1]
        self.assertTrue(tt.alerts_from(rows, FakeUpstream()))

    def test_only_outstanding_releases_alert(self):
        rows = tt.audit(segments(), FakeUpstream())
        keys = {a["key"] for a in tt.alerts_from(rows, FakeUpstream())}
        self.assertTrue(keys)
        self.assertFalse([k for k in keys if k.startswith(("tagged", "out-of-scope"))])

    def test_a_release_inside_its_grace_period_does_not_alert_yet(self):
        import datetime

        class Fresh(FakeUpstream):
            def committed_at(self, sha):
                return datetime.datetime.now(datetime.timezone.utc).isoformat()

        rows = tt.audit(segments(), FakeUpstream())
        self.assertEqual(tt.alerts_from(rows, Fresh()), [])


# --- the command line --------------------------------------------------------

class CommandLine(unittest.TestCase):
    def test_the_modes_are_mutually_exclusive(self):
        parser = tt.build_parser()
        with self.assertRaises(SystemExit):
            parser.parse_args(["--audit", "--alert"])

    def test_write_requires_a_release(self):
        parser = tt.build_parser()
        with self.assertRaises(SystemExit):
            parser.parse_args(["--write"])

    def test_audit_is_the_default_mode(self):
        args = tt.build_parser().parse_args([])
        self.assertFalse(args.alert)
        self.assertIsNone(args.write)

    def test_help_carries_the_policy_so_it_documents_itself(self):
        self.assertIn("Tau Ceti toolchain tags", tt.build_parser().format_help())

    def test_strict_reports_blocked_releases_through_the_exit_code(self):
        args = tt.build_parser().parse_args(["--audit", "--strict", "--json"])
        blocked = [dict(r, status="blocked") for r in tt.audit(segments(), FakeUpstream())[:1]]
        original = tt.audit
        tt.audit = lambda *a, **k: blocked
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(tt._run_audit(args, segments(), FakeUpstream()), 1)
                tt.audit = lambda *a, **k: [dict(blocked[0], status="tagged")]
                self.assertEqual(tt._run_audit(args, segments(), FakeUpstream()), 0)
        finally:
            tt.audit = original


if __name__ == "__main__":
    unittest.main()
