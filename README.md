# copland-avm
Copland Attestation Virtual Machine definition and tools.  This repository contains formal specifications, implementations, and associated proofs for Copland-based tools that support layered remote attestation.  [Copland](https://ku-sldg.github.io/copland/) is a domain-specific language for specifying attestation protocols.  Over time, this repository has grown to support a larger collection of Copland-based tools called MAESTRO (Measurement and Attestation Execution and Synthesis Toolkit for Remote Orchestration).

## Quick Browsing

Using any browser, open the html files in `src/html` to browse all definitions and theorem statements pretty-printed.  All definitions are click-navigable.

## Build Instructions

To compile all the proof script dependencies in `src/` and step through them interactively, make sure you first install:

1.  [Coq](https://github.com/ku-sldg/coq/tree/cakeml-extraction) (Tested on [this](https://github.com/ku-sldg/coq/tree/cakeml-extraction) fork/branch that supports CakeML code extraction)
    * Note:  Make sure this is a LOCAL install (and NOT one installed globally via opam).  This should require:
        * gathering dependencies as specified [here](https://github.com/ku-sldg/coq/blob/cakeml-extraction/INSTALL.md#build-requirements), then 
        *  Inside `<CoqPath>`/coq (top-level of forked Coq repo) run:   `make world`
        *  Add `<CoqPath>/coq/_build/install/default/bin` to your PATH environment variable
        *  Set the COQLIB environment variable to `<CoqPath>/coq/_build/install/default/lib/coq`
        * IMPORTANT:  hide any previous opam-installed versions.  This usually requires deleting a line in your ~/.bashrc (or equivalent) that auto-loads opam tools for each new terminal session.
1.  [VS Code](https://code.visualstudio.com/) (with VSCoq extension), [ProofGeneral](https://proofgeneral.github.io/), or your favorite Coq IDE

Then type:  `cd src ; make`

Once compilation completes (Some warnings are usually ok, but no errors), open the desired `.v` file in `src/` to step through its definitions and proofs (`make` will also re-generate the pretty-printed html in `src/html` for quick browsing).

## Source File Descriptions

### Preamble.v through Main.v are mostly copies of the original Coq source files from the "Orchestrating Layered Attestations" paper [(link)](https://ku-sldg.github.io/copland///resources/copland-post-2019.pdf), with minor modifications for automation and updates to the Copland language.  Those original specs/proofs can be found [here](https://ku-sldg.github.io/copland/software.html).
---
* Preamble.v:  Helper tactics used throughout the proofs.
* More_lists.v:  Facts about lists
* StructTactics.v:  Local copy of structural tactics library from:  https://github.com/uwplse/StructTact
* EqClass.v:  Generic Typeclass for equality, plus some instances
* AbstractedTypes.v:  Abstract (Admitted) definition of a general type for Identifiers and associated abstract values/operations
* Defs.v:  General (non-Copland-specific) automation tactics
* BS.v:  Abstract definition of the raw binary string (`BS`) datatype
* StringT.v:  Abstract type for strings
* OptMonad_Coq.v:  General definition of an option monad + monadic notations
* Maps.v:  Polymorphic, list-based implementation of finite maps
* Term_Defs_Core.v:  Basic definitions for Copland terms, Core terms, Evidence Types, and Copland events
* Params_Admits.v:  Abstract definitions for cryptographic ASP parameters
* Term_Defs.v:  Definitions of main Copland syntactic structures:  phrases(`Term`), Evidence (`Evidence`), events (`Ev`), raw evidence(`RawEv`), type-tagged evidence (`EvC`), evidence semantics (`eval`), annotated phrases (`AnnoTerm`), parallel annotated terms (`AnnoTermPar`), and lemmas about annotation and term well-formedness
* ErrorStringConstants.v:  Abstract place-holders for error string constant definitions
* Anno_Term_Defs.v:  Definition and general properties of Annotated Copland Terms (AnnoTerm)  
* Eqb_Evidence.v:  Decidable equality lemmas for Copland terms and evidence.
* Term.v:  `events` relation mapping phrases and evidence to the attestation-relevant events they generate, various lemmas about events and well-formed phrases.
* Event_system.v:  Abstract event systems (event orderings)
* Term_system.v:  Copland-specific event systems (denotational reference semantics)
* Trace.v:  Event traces and their relation to event systems
* LTS.v:  Small-step, labelled transition system reference semantics for Copland
* Main.v:  Main theorems for Copland reference semantics
* Manifest_Admits.v:  Admitted types, definitions, and typeclass instances related to Manifests
* ErrorStMonad_Coq.v:  General definition of a state monad with error + monadic notations
* Manifest_Set.v:  Definition of the manifest_set datatype, its operations, and related properties
* Manifest.v:  Core definitions of the Manifest, AM_Library, and AM_Config datatypes
* Manifest_Compiler.v:  Implementation of the Manifest Compiler (Manifest + AM_Library --> AM_Config)
* EnvironmentM.v:  Definition of a Manifest Environment mapping (EnvironmentM)
* Manifest_Union.v:  Defining union operations for Manifests and Manifest Environments
* Example_Phrases_Pre_Admits.v:  Admitted parameters for extracted example phrases (used for inline appraisal)
* Example_Phrases_Pre.v:  Example phrases (used for inline appraisal)
* Example_Phrases_Admits.v:  Admitted parameters for extracted example phrases
* Example_Phrases.v:  Example phrases
* ConcreteEvidence.v:  Evidence structure that models concrete results of Copland phrase execution (`EvidenceC`), `Evidence` and `EvidenceC` sub-term relations (`EvSubT` and `EvSub`).
* Cvm_St.v:  Record representing the CVM Monad state structure(`cvm_st`) + CVM monad definition (`CVM`).
* IO_Stubs.v:  Abstract (Admitted) definitions of IO function signatures (measurements, crypto, communication) that must be filled in for a concrete execution.
* Axioms_Io.v:  Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases
* Evidence_Bundlers.v:  Helper functions that simultaneously bundle raw evidence and update a related evidence type structure.  Used by the CVM to update the internal type-tagged evidence structure (`EvC`).  
* Cvm_Monad.v:  CVM Monad monadic helper functions (workhorses of the CVM implementation).
* Cvm_Impl.v:  Top-level monadic function implementing the Copland Compiler/VM (`copland_compile`).
* Cvm_Run.v:  CVM monad run functions.
* Auto.v:  More automation tactics.  Mostly generic, some cvm-monad-specific.
* Manifest_Generator_Helpers.v:  Helper functions used by the Manifest Generator implementation
* Manifest_Generator.v:  Implementation of the Manifest Generator
* Manifest_Generator_Facts.v:  Core properties about the Manifest Generator output
* AutoApp.v:  More automation.
* Helpers_CvmSemantics.v:  Helper lemmas for proofs about the CVM semantics.
* External_Facts.v:  Axioms and lemmas that capture the semantics of external CVM instances.
* Appraisal_Evidence.v:  Functions and lemmas that relate raw and structured evidence, useful for both CVM execution and appraisal.  Also some wrappers/automation for `copland_compile` and annotated terms.
* CvmSemantics.v:  Main proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics. 
* Disclose.v:  Experiments in stating "disclosure" properties of the CVM
* Example_Phrases_Demo_Admits.v:  Admitted parameters for extracted example phrases
* Example_Phrases_Demo.v:  Example phrases
* AM_St.v:  Definitions for AM Monad State (AM_St) and AM Monad (AM)
* Appraisal_IO_Stubs.v:  Abstract (Admitted) definitions of IO function signatures for primitive appraisal checkers
* AM_Monad.v:  Monadic helpers and custom automation for the AM Monad (AM)
* Appraisal_Defs.v:  Helper functions for appraisal procedure +
  predicates used for stating appraisal correctness + predicates
  restricting well-formed phrases and evidence that are appraisable.
* Impl_appraisal.v:  Top-level function implementing appraisal, simultaneous walk over raw evidence and evidence type.  Defined in the option monad for now (lifts to AM monad in extracted code).
* CvmJson_Admits.v:  Admitted definitions of JSON types and conversions to/from strings and Copland datatypes
* ManCompSoundness_Helpers.v:  Helper Lemmas in support of Manifest Compiler Soundness proofs
* ManCompSoundness.v:  Primary results of Manifest Compiler Soundness (for Attestation)
* ManCompSoundness_Appraisal.v:  Primary results for Manifest Compiler Soundness (for Appraisal)
* Manifest_Generator_Union.v:  Combination (unionization) of Manifest Generation for both Attestation and Appraisal
* AM_Helpers.v:  Helper definitions for AM Client and Server implementations
* Client_AM.v:  Implementation of a top-level Client (initiator) thread for Client AMs
* Server_AM.v:  Implementation of a top-level Server (listener) thread for Server AMs
* Extraction_Cvm_Cake.v:  Configuring and invoking custom CakeML code extraction



<!--
* EqClass.v:  Generic Typeclass for equality, plus some instances

* Maps.v:  Polymorphic, list-based implementation of finite maps, borrowed/tweaked from: https://softwarefoundations.cis.upenn.edu/qc-current/TImp.html

* MonadLaws.v:  Proofs of monad laws for the general state monad in GenStMonad.v

* MonadVMFacts.v:  Lemmas and LTAC scripts to leverage facts about the CVM Monad

* StAM.v:  Record representing the AM Monad state structure
* MonadAM.v:  Definition of the AM Monad + monadic helper functions
-->

<!-- ### Copland Compiler and VM specs/proofs -->

## Questions?
Contact author/maintainer (Adam Petz) at: ampetz@ku.edu
