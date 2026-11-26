# Bridge report

Status after this pass:

| declaration in `scratch/BridgeBlind.lean` | status |
| --- | --- |
| `mem_sphere_iff_onCircleM` | proved |
| `blindTransversal_iff` | proved |
| `BlindSecond_eq` | proved |
| `genPosN_blindGenPos` | proved |
| `isGCircleS_of_blindIsGCircle` | proved |
| `chainS_of_blind` | proved |
| `BlindSix_eq` | proved (`rfl`) |
| `N7_RB` | proved without using `RealN7` |
| `N6_RB` | uniqueness half proved; existence half left `sorry` |
| `blindOfChainS` | left `sorry`; see `scratch/BRIDGE_NOTES.md` |
| `N1_RB` | left `sorry`; see `scratch/BRIDGE_NOTES.md` |

Compile command:

```
cd /home/jackagent/paperL_jack && env PATH=/home/jackagent/.elan/bin:$PATH LEAN_PATH=/home/jackagent/paperL_jack lake env lean scratch/BridgeBlind.lean
```

Result: the file parses and type-checks except for the three remaining `sorry` warnings corresponding to the blocked declarations above. No theorem statement was changed. Only files under `scratch/` were touched.

The proved direction `chainS_of_blind` transports the writer predicates to the library predicates by induction on the level; `odd_add_three_iff_mod_two_eq_zero` aligns the two parity conventions. `N7_RB` is proved directly from `Clifford.cospherical_or_collinear` on the three blind second intersections, so it does not need `GenPosN`.

The unresolved direction and the two remaining rows are documented in `scratch/BRIDGE_NOTES.md`.
