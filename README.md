FitchJS
=======

FitchJS is a web app written in JavaScript that lets users to construct proofs in a Fitch-style natural deduction system, and export verified proofs in plain text or LaTeX.  It is a modification of the [LemmoNaDe](https://github.com/mrieppel/LemmoNaDe) program, and implements a similar rule set adapted to a Fitch notation. The fitch proofs are drawn using the [D3.js](http://d3js.org/) library.  If you come across any bugs, please email at: mrieppel at gmail dot com.

A live version of the program is [here](http://mrieppel.github.io/fitchjs/).

Here's a brief description of the content of the various javascript files:

* `script/draw.js`: code to draw the proof as an svg using D3.js.

* `script/parsing.js`: code to parse formulas into trees.  Also contains code for transforming formulas in the "plain" notation into formulas containing unicode characters, and code for generating formulas in latex.  Note that internally, the program expects the "simple" notation, e.g. '>' and '<>', rather than the unicode variants.  Proofs can also only be imported in the plain notation.

* `script/rules_helper.js`: various helper functions needed by the rule checking code. E.g. checking what lines are available from the current line, checking what free variables occur in a line, creating instances of quantified formulas etc.

* `script/rules_pl.js`: code implementing rules of propositional logic.

* `script/rules_ql.js`: code implementing rules of quantificational logic.

* `script/rules_siti_pl.js`: code implementing sequent/theorem introduction (SI/TI) rules.

* `samples/`: contains some sample proofs that can be imported into the program.  The program will export proofs in LaTex markup that compiles using Johan Klüwer's fitch.sty (also included).

* `script/ui.js`: code for the user interface, i.e. to dynamically change which menu item ("Construct Proof", "Export/Import", and "Reference") is active.

* `script/userio.js`: code to capture user input (e.g. to begin a problem, append a line, import a proof etc.) and generate the appropriate output to the html page.  Also contains the global variable that holds the proof.

* `script/validate.js`: code to validate the user input, e.g. checking for well-formedness of input formulas, and to dispatch the user input to the appropriate rule checking code.

Thanks to Fred Mesnard for bug reports!

(c) Michael Rieppel 2015-2017. Released under the MIT License.  See LICENSE above for more information.