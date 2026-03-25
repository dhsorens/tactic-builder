# Tactic Tutorial

This is a tutorial for building tactics in Lean. It contains examples and exercises, for someone who can prove theorems in Lean but cannot yet write tactics.

## Phases

Read through each of these phases and complete the exercises.

- [Phase 1](TacticBuilder/Phase1.lean) - proofs and proof terms. Examples of simple proofs and their corresponding proof terms
- [Phase 2](TacticBuilder/Phase2.lean) - tactics as syntactic wrappers. Some very simple tactics that just serve as wrappers to other tactics, illustrating how `elab ... : tactic` works, how to run existing tactics in your own tactic, and how tactic syntax quotations work.
- [Phase 3](TacticBuilder/Phase3.lean) - basic tactics as proof-term builders. Reimplement minimal versions of basic tactics so you see that each tactic produces a specific proof term or splits the goal into subgoals.
- [Phase 4](TacticBuilder/Phase4.lean) - inspecting the goal and the local context. Working in `TacticM` / `MetaM` with `MVarId`, `Expr`, and the local context.
- [Phase 5](TacticBuilder/Phase5.lean) - typed quotations and antiquotations.
- [Phase 6](TacticBuilder/Phase6.lean) - build tiny automation tactics
- [Phase 7](TacticBuilder/Phase7.lean) - advanced exercises


## Sources:
- [Lean Community](https://leanprover-community.github.io/lean3/extras/tactic_writing.html)
- [Rob Lewis' Video Tutorials](https://www.youtube.com/playlist?list=PLlF-CfQhukNnq2kDCw2P_vI5AfXN7egP2)
- [Hitchiker's Guide to Local Verification](https://github.com/blanchette/logical_verification_2021/raw/main/hitchhikers_guide.pdf)
- [Original paper on metaprogramming](https://leanprover.github.io/papers/tactic.pdf)