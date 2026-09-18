---
## Run 2026-09-18T17:00:13Z

- commit: `345675d90a7ba9c46a777e7e9bb1754a17e6e1b4`

### lake build
```
⚠ [2215/2224] Replayed JSP415.Gerencser
warning: JSP415/Gerencser.lean:15:8: declaration uses `sorry`
warning: JSP415/Gerencser.lean:24:8: declaration uses `sorry`
⚠ [2221/2224] Replayed JSP415.BipLemmas
warning: JSP415/BipLemmas.lean:42:8: declaration uses `sorry`
warning: JSP415/BipLemmas.lean:53:8: declaration uses `sorry`
warning: JSP415/BipLemmas.lean:64:8: declaration uses `sorry`
warning: JSP415/BipLemmas.lean:81:8: declaration uses `sorry`
⚠ [2222/2224] Replayed JSP415.Section3
warning: JSP415/Section3.lean:25:8: declaration uses `sorry`
warning: JSP415/Section3.lean:39:8: declaration uses `sorry`
warning: JSP415/Section3.lean:54:8: declaration uses `sorry`
warning: JSP415/Section3.lean:68:8: declaration uses `sorry`
warning: JSP415/Section3.lean:78:8: declaration uses `sorry`
warning: JSP415/Section3.lean:85:8: declaration uses `sorry`
Build completed successfully (2224 jobs).
```
- build_exit_code: **0**

### sorry / admit occurrences (excluding .lake)
```
lean/JSP415/BipLemmas.lean:48:  sorry
lean/JSP415/BipLemmas.lean:59:  sorry
lean/JSP415/BipLemmas.lean:75:  sorry
lean/JSP415/BipLemmas.lean:92:  sorry
lean/JSP415/Gerencser.lean:20:  sorry
lean/JSP415/Gerencser.lean:28:  sorry
lean/JSP415/Section3.lean:34:  sorry
lean/JSP415/Section3.lean:48:  sorry
lean/JSP415/Section3.lean:63:  sorry
lean/JSP415/Section3.lean:74:  sorry
lean/JSP415/Section3.lean:80:  sorry
lean/JSP415/Section3.lean:89:  sorry
```
- sorry_admit_occurrences: **12**

### #print axioms monochromatic_path_cover
```
'JSP415.monochromatic_path_cover' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### RESULT: RED

