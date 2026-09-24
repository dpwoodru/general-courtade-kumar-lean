# GeneralCK.Certificates.E8TAxisZero0082Root — historical source variant

| | source sha256 | olean sha256 |
|---|---|---|
| published source (`sources/GeneralCK/Certificates/E8TAxisZero0082Root.lean`, compiled by the clean build) | `234eadad7586e12bebce6c9abd673f2d9c3be19123231fd8936c2ea197b301e0` (1,841 B) | `9a158df196b2609fa89c392aec14287ec282698d24b5026e33b08f3664531e8c` (clean build; 133,936 B) |
| campaign variant (`campaign_variant_2b04854f.lean`, this folder) | `2b04854fb7202c589e5e541e8b9009f443f67c5c38737016f09629cacdcc9097` (1,878 B) | `061862a9a429e4e0e614fb9ccc2b0ed54cc01e064d24b721cf9a454d6956dc9c` (original build; 196,496 B) |

- **The difference.** The two sources differ only in the last two lines of the proof of the theorem `positiveAt`:
  - the variant: `norm_num […] at *` then `exact ⟨by linarith, by linarith, by linarith, by linarith⟩`;
  - published: `norm_num […]` then `exact ⟨hs0, hs1, ht0, ht1⟩`.
- **Kernel-level comparison of the two oleans:**
  - imports are equal, and both files have the same 9 constants;
  - 8 constants are kernel-identical;
  - `positiveAt` has the identical type and level parameters but a different proof term.
  - So the theorem statement seen by every downstream module is the same.
- **The clean build.** It compiled the published source (rc 0). No dependent module's bytes changed, and
  `CKRoute.Final` is still byte-identical to the original build's (`43de2287…`).
- **Reproducing the variant.** The variant was also rebuilt canonically against the clean LEAN_PATH, and this
  reproduced the original build's olean `061862a9…` and ilean `0f4136c4…` exactly (`source_variant_evidence.json`).
