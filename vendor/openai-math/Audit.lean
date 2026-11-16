import OAI.InformationTheory.PhotonNumber.Inequality
import OAI.InformationTheory.PhotonNumber.ThermalLimit

/-!
# Audit of the copied openai/math entropy files

Not part of any library. After `lake build OAI`, run from the project root:

  lake env lean vendor/openai-math/Audit.lean

It prints the statements this project intends to build on and the axioms they depend on. The
expected axioms are the three standard ones: `propext`, `Classical.choice`, `Quot.sound`.
-/

open OAI EntropyPhotonNumber

#check @Fock
#check @State
#check @entropy
#check @g
#check @thermalState
#check @thermalState_entropy
#check @diagonalState_entropy
#check @entropy_nonneg
#check @OAI.TensorLp.partialTrace
#check @beamUnitary
#check @beamOutput
#check @entropy_photon_number_inequality

#print axioms thermalState_entropy
#print axioms entropy_nonneg
#print axioms entropy_photon_number_inequality
