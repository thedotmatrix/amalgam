# Amalgam
This project will not be updated for Alloy5.
If you have any questions about this project or related research, please contact:
[Tim Nelson](https://github.com/tnelson)

## Build Instructions (bash scripts or equivalent OS shell commands)
- **KodKod/SATSolvers:** 
  - Run `mksolvers`. 
  - For more detailed instructions, follow [KodKod's Readme](KODKOD.md).
- **Alloy via Command Line:**
  - Run `mkdist`.
  - Run `rundist`. 
  - For more detailed instructions, follow [Alloy's Readme](ALLOY.md).
- **Alloy via Eclipse IDE:**
  - Import > Existing Project > Set root directory to root of this repository > Finish.
  - Run As > Java Application > `src.edu.mit.csail.sdg.alloy4whole.SimpleGUI`
  - Export > Executable Jar File > `src.edu.mit.csail.sdg.alloy4whole.SimpleGUI`

## Reporting Issues
- Building Amalgam: Open a [Build Issue Template](https://github.com/transclosure/Amalgam/issues/new?template=Bug_report.md).
- Running Amalgam: Open a [Feature Issue Template](https://github.com/transclosure/Amalgam/issues/new?template=Feature_request.md).

## Research Modifications
### Features
- **Alternative Model Strategies:** By default, Alloy shows you essentially random examples. Under the options menu, there are now two more example strategies: 1. `minimal` - contains the least facts without invalidating the example 2. `maximal` - contains the most facts without invalidating the example. 
- **Provenance:** For any given example, type `@ln-` into the evaluator, to see what's locally necessary: the facts that must be true/false for the example to be valid. If the locally necessary fact is true in the example, you can ask `@why` this fact is true in the example; if it is false in the example, you can ask `@whynot`. The answer is a proof of local necessity, that highlights the parts of the specification that led to the fact being locally necessary. 
- **Coverage:** Not currently live. See Issue #1 for more information. 
- **Telemetry:** All interactions with Amalgam are logged in the Amalgam folder of your OS's temporary directory. If you are having trouble finding your temporary directory, in the Amalgam options, change the solver to `output cnf`, and see Amalgams console for where the file is saved. You should find an `AMALGAM.log` in the same directory. 
- **Less Options, Less Ambiguous Semantics:** for the sake of our user studies, sanity checking, and own research, some of the Alloy options usually on by default (such as symmetry breaking) has been turned off and disabled by default. These can be enabled by modifying the code, or by running `src.edu.mit.csail.sdg.alloy4whole.PreferencesDialog` instead of `src.edu.mit.csail.sdg.alloy4whole.SimpleGUI`. 
### Code Changes
See the `MODIFY` and `DISABLE` eclipse tasklist (or ctrl+F) tags on every line of code that has been added or changed.
