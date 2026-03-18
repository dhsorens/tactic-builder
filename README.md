# Tactic Building

Some examples of building tactics in Lean, for someone who can prove theorems in Lean but cannot yet write tactics.

## Phases

- Phase 1 - proofs and proof terms. Examples of simple proofs and their corresponding proof terms
- Phase 2 - tactics as syntactic wrappers. Some very simple tactics that just serve as wrappers to other tactics, illustrating how `elab ... : tactic` works, how to run existing tactics in your own tactic, and how tactic syntax quotations work.
- Phase 3 - tactics that inspect the proof goal a little. 
- Phase 4 - typed quotations and antiquotations
- Phase 5 - build tiny automation tactics


## Sources:
- [Lean Community](https://leanprover-community.github.io/lean3/extras/tactic_writing.html)
- [Rob Lewis' Video Tutorials](https://www.youtube.com/playlist?list=PLlF-CfQhukNnq2kDCw2P_vI5AfXN7egP2)
- [Hitchiker's Guide to Local Verification](https://github.com/blanchette/logical_verification_2021/raw/main/hitchhikers_guide.pdf)
- [Original paper on metaprogramming](https://leanprover.github.io/papers/tactic.pdf)