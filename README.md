# Finitary Physical Mathematics (FPM)

A formal, resource-bounded framework for physical modeling implemented in Lean.

## Overview
Finitary Physical Mathematics (FPM) is a foundational engine proposed as possible alternative solution to resolve the problems in physics caused by the infinitary axioms of classical Zermelo-Fraenkel set theory (ZFC). Within FPM, mathematical objects are not treated as completed infinitary entities, but as algorithmic, generative observables constrained by explicit spatial and temporal resource budgets. 

*Note: To fully understand the theoretical intention and motivation behind this code, please read the foundational paper using the DOI link provided in the citation section below.*

## Compiler Phases
The FPM framework is structured into seven distinct operational phases within the Lean compiler:
* **Phase 1: Core Primitives** - Establishes the basic precision budget (`Context`) and the `FPM_Real` generator, which is bounded by thermodynamic stabilization rates.
* **Phase 2: Arithmetic Generators** - Implements resource-bounded binary and unary operations with rigorous bounds on error expansion.
* **Phase 3: The Classical Bridge** - Translates foundational ZFC theorems into the finitary framework using thermodynamically stable sequence tails.
* **Phases 4 & 5: Automated Tactic Engine** - Introduces custom Lean tactics (`fpm`, `fpm_from`) to automatically calculate upstream precision shifts and manage context weakening.
* **Phase 6: Advanced Modeling** - Extends the finitary real engine to handle complex numbers, finite vectors, matrices, tensors, and basic calculus.
* **Phase 7: Physical Applications** - Tests the compiler with a dynamical physical model (a local oscillator), tracking energy observables across a two-chart atlas.

## Requirements
To run and explore the compiler, you will need:
* **Lean Version:** `4.28`

In case the code does not successfully compiles due to issues in uploading the lean-toolchain, or lakefile.toml, kindly only use the files FPM_Phase1 till FPM_Phae7_Phy and let lean build its own dependendent files.

## Development Notes
Please note that this is my first mathematical project written in Lean, so the code structure may not be perfectly clean or strictly idiomatic yet. Additionally, I utilized AI to assist with the development process, and approximately 60% of the code was written with AI assistance. 

Despite this, the implementation has been rigorously tested: **it can be ensured that the code is mathematically correct and fully compiles** under Lean 4.28 without errors.

## Contact
If you have any questions regarding the framework, the proofs, or the Lean implementation, please feel free to write to me at: **saziz.bee22seecs@seecs.edu.pk**

## Citation
To cite this work, please use the following DOI for the paper: [10.5281/zenodo.19634093](https://doi.org/10.5281/zenodo.19634093)
