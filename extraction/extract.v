From Coq Require Import Extraction ExtrOcamlString ExtrOcamlBasic.
From WiSE Require Import streams implem.bugfinder symbolic.solver.

Cd "./extraction".
Extraction "loop.ml" find_bugs find_bugs_assuming peek bsimp.
Cd "../".