module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesRingEquivConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHilbertLatticeTwistIffLiftStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValue

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutEmbInjective

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

noncomputable def autEmb {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) : Emb F :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).embedding

theorem autEmb_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) (y : F) :
    ((autEmb g i y : ℝ) : ℂ) = g ((i y : ℝ) : ℂ) :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).coe_embedding_apply y

theorem autEmb_injective {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) :
    Function.Injective (autEmb (F := F) g) := by
  intro i j h
  ext y
  have h1 : g ((i y : ℝ) : ℂ) = g ((j y : ℝ) : ℂ) := by
    rw [← autEmb_apply, ← autEmb_apply, h]
  exact_mod_cast g.injective h1

theorem aut_perm_emb : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ),
    ∃ π : Equiv.Perm (Emb F), ∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ) := by
  intro F _ _ _ g
  refine ⟨Equiv.ofBijective (autEmb g) (Finite.injective_iff_bijective.mp (autEmb_injective g)), ?_⟩
  intro i y
  exact (autEmb_apply g i y).symm

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesRingEquivConjStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertEisensteinSeries_ringEquiv_conj : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (Emb F)) (κ : Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → 0 < N → IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → HasLevel N (split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (PowerSeries.coeff n (hser k N 𝔞 a x κ c)) = PowerSeries.coeff n (hser k N 𝔞 a (m * x) (fun j ↦ κ (π.symm j)) (fun n ↦ g (c n))) := by
  first | exact @GlobalTheory.HilbFam.hser_conj | exact GlobalTheory.HilbFam.hser_conj | (intros; apply GlobalTheory.HilbFam.hser_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSplitLatticeTwistDiagonalCoprime

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem twist_split_diagonal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by
  intro F _ _ _ N 𝔞 𝔟 x a hcop hlev
  have hstd : ∀ w : Fin 2 → F, w ∈ stdLat F ↔ ∀ i, w i ∈ (1 : Submodule (𝓞 F) F) := by
    intro w; simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  have hsp : ∀ (z : F) (w : Fin 2 → F), w ∈ split 𝔞 𝔟 z ↔
      w 0 ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F) ∧
      w 1 - w 0 * z ∈ (latM 𝔞 : Submodule (𝓞 F) F) := fun _ _ ↦ Iff.rfl
  have hA : (Matrix.diagonal ![1, (a : ZMod N)]) =
      (Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → ZMod N) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hv0 : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → F)) = ![y 0, a * y 1] := by
    intro y
    ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  have hN : ∀ w ∈ stdLat F, (N : F) • w ∈ split 𝔞 𝔟 x := by
    intro w hw
    have h := hlev.1 w hw
    rw [Nat.cast_smul_eq_nsmul] at h ⊢
    exact h
  have hz : ∀ (n : ℤ) (S : Submodule (𝓞 F) F) (m : F), m ∈ S → (n : F) * m ∈ S := by
    intro n S m hm
    rw [← zsmul_eq_mul]
    exact zsmul_mem hm n
  ext v
  rw [hA, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ _ v hlev.2]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    rw [hv0]
    have hw' := (hstd w).1 hw
    have h0 := (hsp _ _).1 (hN ![w 0, 0] ((hstd _).2 (by
      intro i; fin_cases i
      · exact hw' 0
      · exact Submodule.zero_mem _)))
    have h1 := (hsp _ _).1 (hN ![0, w 1] ((hstd _).2 (by
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hw' 1)))
    have hy' := (hsp _ _).1 hy
    rw [hsp]
    refine ⟨?_, ?_⟩
    · have := Submodule.add_mem _ hy'.1 h0.1
      convert this using 1
      simp
    · have := Submodule.add_mem _ (Submodule.add_mem _ (hz a _ _ hy'.2) h1.2) (hz a _ _ h0.2)
      convert this using 1
      simp
      ring
  · intro hv
    have hv' := (hsp _ _).1 hv
    obtain ⟨u, t, hut⟩ := hcop
    have hut' : (u : F) * a + t * N = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → F) hut
    have hm : ![0, v 1 - v 0 * (a * x)] ∈ split 𝔞 𝔟 x := by
      rw [hsp]
      refine ⟨Submodule.zero_mem _, ?_⟩
      convert hv'.2 using 1
      simp
    have hm' := (hstd _).1 (hlev.2 hm) 1
    refine ⟨![v 0, v 0 * x + u * (v 1 - v 0 * (a * x))], ?_, ![0, t * (v 1 - v 0 * (a * x))], ?_, ?_⟩
    · rw [hsp]
      refine ⟨hv'.1, ?_⟩
      convert hz u _ _ hv'.2 using 1
      simp
    · rw [hstd]
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hz t _ _ hm'
    · rw [hv0]
      ext j; fin_cases j
      · simp
      · simp
        linear_combination (-(v 1 - v 0 * (a * x))) * hut'

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSplitLatticeTwistDiagonalCoprimeStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertSplitLattice_twist_diagonal_coprime : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by
  first | exact @GlobalTheory.HilbFam.twist_split_diagonal | exact GlobalTheory.HilbFam.twist_split_diagonal | (intros; apply GlobalTheory.HilbFam.twist_split_diagonal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficients

section

@[expose] public section

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem qConj_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (m : ℤ) (κ κ' : Emb F → ℕ) (Ch Ch' : ℍ → ℂ), IsCoprime m (N : ℤ) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ i j : Emb F, (∀ y : F, g ((i y : ℝ) : ℂ) = ((j y : ℝ) : ℂ)) → κ' j = κ i) → QConj g N Ch Ch' → QConj g N (hfun (2 * s) L κ Ch) (hfun (2 * s) (twist N L (Matrix.diagonal ![1, (m : ZMod N)])) κ' Ch') := by
  intro hE F _ _ _ hf s N L hs hN hL z hz g m κ κ' Ch Ch' hm hg hκ hC
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := exists_eq_split_of_hasLevel F N L hN hL
  have htw := GlobalTheory.T.hilbertSplitLattice_twist_diagonal_coprime F N 𝔞 𝔟 x m hm hL
  have hL' := hasLevel_twist_of_hasLevel F N _ (Matrix.diagonal ![1, (m : ZMod N)]) hL
  rw [htw] at hL' ⊢
  obtain ⟨Z, a, hZ, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  have h0 := constTerm_eq_zetaVal F (2 * s) z _ Z (by omega) hz hZ
  obtain ⟨π, hπ⟩ := aut_perm_emb F g
  have hκ' : κ' = fun j ↦ κ (π.symm j) := by
    funext j
    refine hκ (π.symm j) j fun y ↦ ?_
    rw [hπ, Equiv.apply_symm_apply]
  obtain ⟨c, hc, hc'⟩ := hC
  have hev : Even (2 * s) := even_two_mul s
  refine ⟨_, GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN hev ha hL hc, ?_⟩
  have h2 := GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a (m * x) N κ' Ch' _ hN hev ha hL' hc'
  have h3 := fun n ↦ GlobalTheory.T.hilbertEisensteinSeries_ringEquiv_conj F (2 * s) 𝔞 𝔟 _ a x s N g m π κ c n rfl hN ha
    (by rw [h0, map_ratCast]) hL hg hπ
  simp only [h3]
  rw [hκ'] at h2 ⊢
  exact h2

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficientsStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_galois_conj_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (m : ℤ) (κ κ' : Emb F → ℕ) (Ch Ch' : ℍ → ℂ), IsCoprime m (N : ℤ) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ i j : Emb F, (∀ y : F, g ((i y : ℝ) : ℂ) = ((j y : ℝ) : ℂ)) → κ' j = κ i) → QConj g N Ch Ch' → QConj g N (hfun (2 * s) L κ Ch) (hfun (2 * s) (twist N L (Matrix.diagonal ![1, (m : ZMod N)])) κ' Ch') := by
  first | exact @GlobalTheory.HilbFam.qConj_hfun_twist | exact GlobalTheory.HilbFam.qConj_hfun_twist | (intros; apply GlobalTheory.HilbFam.qConj_hfun_twist <;> assumption)
end
end
