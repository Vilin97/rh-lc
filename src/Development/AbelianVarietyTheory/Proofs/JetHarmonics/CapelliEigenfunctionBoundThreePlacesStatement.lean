module

public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
public import Formalism.HermitianCurvature.HerGenC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Formalism.HermitianCurvature.StatementTBB
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSumOfCompactCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetBoundEqualTypesThreePlacesOfXiIntegrableStatement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPowSmulCompPolyFamilyEigenSu
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormLeNormCOfEigenSum
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoLevelZeroFormCutoffPowMulOfDominationStatement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqNF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
import Mathlib.Algebra.Order.Star.Real
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSumOfCompactCoefficientPositivityStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.latticeSum_of_compactCoefficient_positivity : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base G → (∀ y, 0 < nn y) → TBB.BlockGrowthBound p nn G Y K N := by
  first | exact @GlobalTheory.LatticeGerm.latticeSum_of_cptCoef | exact GlobalTheory.LatticeGerm.latticeSum_of_cptCoef | (intros; apply GlobalTheory.LatticeGerm.latticeSum_of_cptCoef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPowSmulCompPolyFamilyEigenSuStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.capelliEigenfunction_pow_smul_comp_polyFamily_eigenSum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (lam : Fin (2 * r + k + 1) → ℝ) (A₀ : ℝ) (p₀ dA : ℕ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (Aop : B.Mat k r → (Wq' →L[ℂ] Wq)), (∀ s t, s ≠ t → 2 * (((2 * r + 2) * p₀ + dA : ℕ) : ℝ) < |lam s - lam t|) → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A₀) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat k r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq' →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ (((2 * r + 2) * p₀ + dA : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A₀ - (((2 * r + 2) * p₀ + dA : ℕ) : ℝ)) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (fun g => ((Gf k r z z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) g = ∑ i, Fi i g) := by
  first | exact @GlobalTheory.gfPow_smul_comp_polyOp_eigenSum | exact GlobalTheory.gfPow_smul_comp_polyOp_eigenSum | (intros; apply GlobalTheory.gfPow_smul_comp_polyOp_eigenSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.EnergyBoundPolynomialWeightPowCapelliEigen

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem energy_bound_gfPow_smul_comp_polyOp : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wf : Type) [NormedAddCommGroup Wf] [InnerProductSpace ℂ Wf] [FiniteDimensional ℂ Wf] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wf →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq →L[ℂ] Wf)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq →L[ℂ] Wf)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g))).re := by
  intro hXi Wp Wq _ _ _ _ _ _ Wf _ _ _ P p lam lam' cs A₀ p₀ dA nn f Aop Y N hA hC hI hE hgap hcl hAB hnn
    w hw hN
  have hgap' : ∀ s t, s ≠ t →
      2 * (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) < |lam' s - lam' t| := by
    intro s t hst
    have h1 := hgap s t hst
    have h2 := hcl s
    have h3 := hcl t
    have h4 : |lam s - lam t| ≤ |lam' s - lam' t| + |lam' s - lam s| + |lam' t - lam t| := by
      have e : lam s - lam t = (lam' s - lam' t) - (lam' s - lam s) + (lam' t - lam t) := by ring
      rw [e]
      have a1 := abs_add_le ((lam' s - lam' t) - (lam' s - lam s)) (lam' t - lam t)
      have a2 := abs_sub (lam' s - lam' t) (lam' s - lam s)
      linarith
    linarith
  have hes := GlobalTheory.T.capelliEigenfunction_pow_smul_comp_polyFamily_eigenSum P.k P.r Wp Wf Wq p.T.base.z p.T.base.z' lam' A₀ p₀ dA f Aop hgap'
    ⟨hC, hI⟩ hE hA
  refine GlobalTheory.levelZero_form_le_normC_of_eigen_sum hXi Wp Wq P p lam' ((2 * P.r + 2) * p₀ + dA) _ nn _ Y N hAB hes ?_ w hw hN
  intro y
  refine le_trans (Finset.prod_le_prod₀ (fun s _ => by positivity) (fun s _ => ?_)) (hnn y)
  have h2 := hcl s
  have e : y + lam' s = (y + lam s) + (lam' s - lam s) := by ring
  have a1 := abs_add_le (y + lam s) (lam' s - lam s)
  rw [e]
  linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.EnergyBoundPolynomialWeightPowCapelliEigenStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wf : Type) [NormedAddCommGroup Wf] [InnerProductSpace ℂ Wf] [FiniteDimensional ℂ Wf] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wf →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq →L[ℂ] Wf)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq →L[ℂ] Wf)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g))).re := by
  first | exact @GlobalTheory.energy_bound_gfPow_smul_comp_polyOp | exact GlobalTheory.energy_bound_gfPow_smul_comp_polyOp | (intros; apply GlobalTheory.energy_bound_gfPow_smul_comp_polyOp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyBoundDecayingCasimirEigenfunction

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem limBd_fpm_and_fpmSh : GlobalTheory.HCXi.BesselXiIntegrable → (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd p nn (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N) ∧ (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (P : M.Par) (u u' : ℕ → ℝ) (q : KB.Pl (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') Wp Wq') (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd q nn (Formalism.FourierDecayAlt.P.CutBP2.fpmSh q f Aop p₀) Y N) := by
  intro hXi
  refine ⟨?_, ?_⟩
  · intro Wp Wq _ _ _ _ _ _ P p lam lam' cs A₀ p₀ nn f Y N h1 h2 h3 h4 h5 h6 h7
    refine GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen hXi Wp Wq Wq P p lam lam' cs A₀ p₀ 0 nn f
      (fun _ => ContinuousLinearMap.id ℂ Wq) Y N ?_ h1 h2 h3 h4 h5 h6 h7
    refine ⟨1, fun _ _ => 1, fun _ => ContinuousLinearMap.id ℂ Wq, fun _ => ?_, fun g => by simp⟩
    exact ⟨1, by simp, fun g => by simp⟩
  · intro Wp Wq _ _ _ _ _ _ Wq' _ _ _ P u u' q lam lam' cs A₀ p₀ dA nn f Aop Y N h0 h1 h2 h3 h4 h5 h6 h7
    exact GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen hXi Wp Wq' Wq (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') q lam lam' cs A₀ p₀ dA nn f Aop Y N
      h0 h1 h2 h3 h4 h5 h6 h7

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyBoundDecayingCasimirEigenfunctionStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.levelZeroEnergyBound_decayingCasimirEigenfunction : GlobalTheory.HCXi.BesselXiIntegrable → (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd p nn (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N) ∧ (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (P : M.Par) (u u' : ℕ → ℝ) (q : KB.Pl (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') Wp Wq') (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd q nn (Formalism.FourierDecayAlt.P.CutBP2.fpmSh q f Aop p₀) Y N) := by
  first | exact @GlobalTheory.limBd_fpm_and_fpmSh | exact GlobalTheory.limBd_fpm_and_fpmSh | (intros; apply GlobalTheory.limBd_fpm_and_fpmSh <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionBoundThreePlaces

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.EigenThreePlaces

theorem exists_isCut0 : ∃ χ : ℝ → ℝ, C6.IsCut0 χ := by
  refine ⟨fun x => Real.smoothTransition (2 * x - 1), ?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

theorem decay_split (c c' x : ℝ) (k r N : ℕ)
    (h : max 3 (max c c') * ((r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ x) :
    c * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ x ∧
      c' * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ x ∧
      B.AB k r ≤ x := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hn1 : 1 ≤ n := by linarith
  have hX : 0 ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by positivity
  have hR : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
  refine ⟨le_trans ?_ h, le_trans ?_ h, le_trans ?_ h⟩
  · gcongr
    exact (le_max_left _ _).trans (le_max_right _ _)
  · gcongr
    exact (le_max_right _ _).trans (le_max_right _ _)
  · have h1 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    have h2 : n ≤ n ^ 3 := le_self_pow₀ hn1 (by norm_num)
    have h3 : n ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by
      have : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
      linarith
    calc B.AB k r ≤ 3 * ((r : ℝ) + 1) * n := by
          unfold B.AB
          rw [hn]
          nlinarith [mul_nonneg hr hk, mul_nonneg hr hr]
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _

theorem main : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → N ≤ 2 * p₀ → ∀ (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs : ℝ), (∀ y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (y : ℂ) f g = ((∏ s, (y + lam' s) : ℝ) : ℂ) • f g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) ≤ cs - 1) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnp y) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnm y) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hX hP hDom Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, Cc, h⟩ := GlobalTheory.T.jetBound_equalTypes_threePlaces_of_xiIntegrable hX hP Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := GlobalTheory.T.tendsto_levelZero_form_cutoff_pow_mul_of_domination hX hP hDom Cb
  obtain ⟨-, L2⟩ := GlobalTheory.T.levelZeroEnergyBound_decayingCasimirEigenfunction hX
  obtain ⟨χ, hχ⟩ := exists_isCut0
  refine ⟨C₄, max 3 (max Cc Cn), ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d
    nnp nnm Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hnnp hnnm hDDp hDDm hf hfA hAp hAm
    hth hAms hreg hWGp hLGp hWGm hLGm hN2 lam lam' cs he hs hc hnp hnm
  obtain ⟨hth1, hth4, hth3⟩ := decay_split Cc Cn _ P.k P.r N hth
  have hth4' : Cn * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      (A₀ - d) - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hA3 : B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) := by
    rw [Nat.cast_add]; linarith
  have hLp : LimEvT pp χ (fpmSh pp f Ap p₀) Yp N := by
    have e := fpmSh_eq_fpm pp f Ap p₀
    have k := hn Wp Wqp (shP P up up') pp (fun g => (f g).comp (Ap g)) (A₀ - d) p₀ χ Yp N
      ⟨hχ, hDDp, ckOn_compSh hf (ckOn_of_polyOp hAp), inCC_compSh pp hfA hAp, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT pp χ F Yp N) e) k
  have hLm : LimEvT pm χ (fpmSh pm f Am p₀) Ym N := by
    have e := fpmSh_eq_fpm pm f Am p₀
    have k := hn Wp Wqm (shP P um um') pm (fun g => (f g).comp (Am g)) (A₀ - d) p₀ χ Ym N
      ⟨hχ, hDDm, ckOn_compSh hf (ckOn_of_polyOp hAm), inCC_compSh pm hfA hAm, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT pm χ F Ym N) e) k
  have hI5p : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N := fun ε hε n =>
    GlobalTheory.T.latticeSum_of_compactCoefficient_positivity hP Wp Wqp (shP P up up') pp nnp _ Yp K N Cb hDDp
      (cptCoef_apx (shP P up up') pp.T.base hχ (ckOn_fpmSh pp p₀ hf (ckOn_of_polyOp hAp)) hε n) hnnp
  have hI5m : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N := fun ε hε n =>
    GlobalTheory.T.latticeSum_of_compactCoefficient_positivity hP Wp Wqm (shP P um um') pm nnm _ Ym K N Cb hDDm
      (cptCoef_apx (shP P um um') pm.T.base hχ (ckOn_fpmSh pm p₀ hf (ckOn_of_polyOp hAm)) hε n) hnnm
  exact h P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d
    χ nnp nnm Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hfA hAp hAm
    hth1 hAms hreg hWGp hLGp hWGm hLGm hI5p hI5m hLp hLm
    (L2 Wp Wq Wqp P up up' pp lam lam' cs A₀ p₀ d nnp f Ap Yp N hAp hf hfA he hs hc hA3 hnp)
    (L2 Wp Wq Wqm P um um' pm lam lam' cs A₀ p₀ d nnm f Am Ym N hAm hf hfA he hs hc hA3 hnm)

end GlobalTheory.EigenThreePlaces
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionBoundThreePlacesStatement

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.capelli_eigenfunction_bound_three_places : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → N ≤ 2 * p₀ → ∀ (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs : ℝ), (∀ y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (y : ℂ) f g = ((∏ s, (y + lam' s) : ℝ) : ℂ) • f g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) ≤ cs - 1) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnp y) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnm y) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  first | exact @GlobalTheory.EigenThreePlaces.main | exact GlobalTheory.EigenThreePlaces.main | (intros; apply GlobalTheory.EigenThreePlaces.main <;> assumption)
end
end
