import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeXiMulDpowSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeDpowClosedOfHyp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeIdealIffSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsDPMorphismOfCompat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationTopEqBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLTorsionFreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeNatDividesLPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationFg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIdealIsPrime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIdealQuotientChain
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLPowMemSpanOfNotMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsAdicComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLAdicClosed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open DividedPowers

namespace CrystallineSemistableComparison.Pb.Lat

section Lat
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dp_ι (hc : DPClosed (ι f ξ l M) (γB f ξ)) : IsDPMorphism (γ f ξ l M hc) (γB f ξ) (ι f ξ l M) :=
  ⟨Ideal.map_le_iff_le_comap.2 fun _ hx => hx, fun {n} a ha => (ι_γ f ξ l M hc ha).symm⟩

end Lat

section Map
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

end Map

end CrystallineSemistableComparison.Pb.Lat
