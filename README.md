# Tactic Tutorial

This is a tutorial for building tactics in Lean. It contains examples and exercises, for someone who can prove theorems in Lean but cannot yet write tactics.

## Phases

Read through each of these phases and complete the exercises.

- [Phase 1](TacticBuilder/Phase1.lean) - proofs and proof terms. Examples of simple proofs and their corresponding proof terms
- [Phase 2](TacticBuilder/Phase2.lean) - tactics as syntactic wrappers. Some very simple tactics that just serve as wrappers to other tactics, illustrating how `elab ... : tactic` works, how to run existing tactics in your own tactic, and how tactic syntax quotations work.
- [Phase 3](TacticBuilder/Phase3.lean) - tactics that inspect the proof goal a little. 
- [Phase 4](TacticBuilder/Phase4.lean) - typed quotations and antiquotations
- [Phase 5](TacticBuilder/Phase5.lean) - build tiny automation tactics
- [Phase 6](TacticBuilder/Phase6.lean) - advanced execrises


## Sources:
- [Lean Community](https://leanprover-community.github.io/lean3/extras/tactic_writing.html)
- [Rob Lewis' Video Tutorials](https://www.youtube.com/playlist?list=PLlF-CfQhukNnq2kDCw2P_vI5AfXN7egP2)
- [Hitchiker's Guide to Local Verification](https://github.com/blanchette/logical_verification_2021/raw/main/hitchhikers_guide.pdf)
- [Original paper on metaprogramming](https://leanprover.github.io/papers/tactic.pdf)