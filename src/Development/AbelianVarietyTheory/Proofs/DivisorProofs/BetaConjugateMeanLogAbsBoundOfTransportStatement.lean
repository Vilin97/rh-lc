module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateCmValueCharacterPermutedWeightStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormPowSixMulDiscriminantClassInvStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCmConstantAddLogDerivativeLeSquareTopBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormConjugatesOverIdealClassesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassMeanLogNormDiscChowlaSelberg

section

@[expose] public section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

namespace GlobalTheory.ClassMeanDisc

theorem classMean_log_norm_disc : ∀ (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → discr K = -(D.host.d : ℤ) → 4 < D.host.d → ∀ (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : ClassGroup (𝓞 K) → PeriodPair), (∀ c, ClassGroup.mk K (rep c) = c) → (∀ c, IsLatOf φK (rep c : FractionalIdeal (𝓞 K)⁰ K) (L c)) → (∑ c, Real.log (nrm (rep c : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (L c)‖)) / (classNumber K : ℝ) = 12 * Real.log (2 * Real.pi) - 6 * Real.log D.host.d + 6 * Real.eulerMascheroniConstant - 6 * Formalism.BasicNotions.dlogL D 1 := by
  intro D K _ _ φK h2 hD hd rep L hrep hL
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd3 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hχ : IsKroneckerChar (Formalism.BasicNotions.chiK D) := isKroneckerChar_quadraticChar hd3
  have key := chowla_selberg_discriminant h2 hD hd hχ φK hrep hL
  have hre := congrArg Complex.re key
  simp only [Complex.ofReal_re, Complex.sub_re] at hre
  unfold Formalism.BasicNotions.dlogL nrm latDisc
  rw [hre]
  simp [Complex.mul_re]

end GlobalTheory.ClassMeanDisc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassMeanLogNormDiscChowlaSelbergStatement

section

@[expose] public section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.classMean_log_norm_disc_chowlaSelberg : ∀ (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → discr K = -(D.host.d : ℤ) → 4 < D.host.d → ∀ (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : ClassGroup (𝓞 K) → PeriodPair), (∀ c, ClassGroup.mk K (rep c) = c) → (∀ c, IsLatOf φK (rep c : FractionalIdeal (𝓞 K)⁰ K) (L c)) → (∑ c, Real.log (nrm (rep c : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (L c)‖)) / (classNumber K : ℝ) = 12 * Real.log (2 * Real.pi) - 6 * Real.log D.host.d + 6 * Real.eulerMascheroniConstant - 6 * Formalism.BasicNotions.dlogL D 1 := by
  first | exact @GlobalTheory.ClassMeanDisc.classMean_log_norm_disc | exact GlobalTheory.ClassMeanDisc.classMean_log_norm_disc | (intros; apply GlobalTheory.ClassMeanDisc.classMean_log_norm_disc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagQuadraticSubfieldOfToricCMFieldData

section

@[expose] public section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped IntermediateField

namespace GlobalTheory.QuadInHost

theorem exists_quadField : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by
  intro E _ _ I _ d φ hF hd4 Λ hΛ
  obtain ⟨hp, hd, -, -, -, hI, -, w, hw, hφw⟩ := hF
  have hd0 : (0 : ℚ) < d := by exact_mod_cast hp.pos
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  have hm : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ).Monic := by monicity!
  have he : Polynomial.aeval w (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ) = 0 := by
    simp [hw]
  have hi : IsIntegral ℚ w := ⟨_, hm, he⟩
  have h2 : Module.finrank ℚ ℚ⟮w⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hi]
    refine le_antisymm ((Polynomial.natDegree_le_natDegree (minpoly.min ℚ w hm he)).trans
      (by compute_degree)) ((minpoly.two_le_natDegree_iff hi).2 ?_)
    rintro ⟨q, hq⟩
    have h1 : (algebraMap ℚ E q) ^ 2 = -(d : E) := by rw [hq]; exact hw
    have h3 : q ^ 2 = -(d : ℚ) := (algebraMap ℚ E).injective (by simpa using h1)
    nlinarith [sq_nonneg q]
  let r : ℚ⟮w⟯ := IntermediateField.AdjoinSimple.gen ℚ w
  have hr : r ^ 2 = -(d : ℚ⟮w⟯) := Subtype.ext (by simpa [r] using hw)
  let φK : ℚ⟮w⟯ →+* ℂ := (φ i₀).comp (algebraMap ℚ⟮w⟯ E)
  have hφr : ∀ i, (φ i).comp (algebraMap ℚ⟮w⟯ E) r = Complex.I * (Real.sqrt d : ℂ) := fun i => hφw i
  have hsq : (Real.sqrt d : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hp.pos)
    exact_mod_cast this.ne'
  refine ⟨ℚ⟮w⟯, h2, GlobalTheory.discr_eq_neg_of_sq_eq h2 hp.squarefree hd4 hr, φK, ?_, ?_, ?_⟩
  · intro i
    have := (IntermediateField.adjoin.powerBasis hi).algHom_ext
      (f := ((φ i).comp (algebraMap ℚ⟮w⟯ E)).toRatAlgHom) (g := φK.toRatAlgHom)
      (by simp only [IntermediateField.adjoin.powerBasis_gen]; exact (hφr i).trans (hφr i₀).symm)
    exact congrArg AlgHom.toRingHom this
  · intro h
    have := congrArg (fun f => f r) h
    simp only [RingHom.comp_apply] at this
    change starRingEnd ℂ (φK r) = φK r at this
    rw [show φK r = _ from hφr i₀] at this
    simp [Complex.conj_ofReal] at this
    have h0 : (2 * Complex.I) * (Real.sqrt d : ℂ) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h0 with h0 | h0
    · simp at h0
    · exact hsq h0
  · obtain ⟨ω, hω2, hgen⟩ := GlobalTheory.exists_integer_generator_of_sq_eq_neg h2 hp.squarefree hd4 hr
    have hφω : φK ω = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 := by
      have := congrArg φK hω2
      rw [map_mul, map_add (f := _), map_one, map_ofNat, show φK r = _ from hφr i₀] at this
      linear_combination this / 2
    unfold IsLatOf
    ext x
    rw [SetLike.mem_coe, hΛ x]
    constructor
    · rintro ⟨hx, a, b, rfl⟩
      let y : ℚ⟮w⟯ := a + b * r
      have hy : φK y = a + b * (Complex.I * (Real.sqrt d : ℂ)) := by
        simp only [y, map_add (f := _), map_mul, map_ratCast, show φK r = _ from hφr i₀]
      have hint : IsIntegral ℤ y := by
        rw [← hy] at hx
        exact (isIntegral_algHom_iff φK.toIntAlgHom φK.injective).1 hx
      refine ⟨y, ?_, hy⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨⟨y, hint⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff] at hy
      obtain ⟨c, rfl⟩ := hy
      refine ⟨(RingOfIntegers.isIntegral_coe c).map φK.toIntAlgHom, ?_⟩
      obtain ⟨m, n, rfl⟩ := hgen c
      refine ⟨m + n / 2, n / 2, ?_⟩
      change φK ((m + n * ω : 𝓞 ℚ⟮w⟯) : ℚ⟮w⟯) = _
      push_cast
      simp only [map_add (f := _), map_mul, hφω]
      simp
      ring

end GlobalTheory.QuadInHost
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagQuadraticSubfieldOfToricCMFieldDataStatement

section

@[expose] public section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport

theorem _root_.GlobalTheory.T.exists_imagQuadratic_subfield_of_toricCMFieldData : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by
  first | exact @GlobalTheory.QuadInHost.exists_quadField | exact GlobalTheory.QuadInHost.exists_quadField | (intros; apply GlobalTheory.QuadInHost.exists_quadField <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransport

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open scoped nonZeroDivisors

namespace GlobalTheory.BetaArchPf

theorem host_d_mod' (D : Formalism.BasicNotions.D7) : D.host.d % 4 = 3 := by
  have := D.host.hyp.2.2.2.1; omega

theorem toric_eq_L {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E} {Λ : ℂ → ℂ} (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s)
    (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ) (hΛ : IsHeckeL χ Λ) : IsToricSum φ s κ (condQ 𝔣 ∅) χ (Λ s) := by
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 ∅ χ
    (fun _ => P₀) Λ hU hs hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rwa [Finset.filter_empty, Finset.prod_empty, mul_one] at t1

theorem condQ_empty {E : Type} [Field E] [NumberField E] (𝔣 : Ideal (OF E)) : condQ 𝔣 ∅ = 𝔣 := by
  simp [condQ]

end GlobalTheory.BetaArchPf

namespace GlobalTheory.SqTop


open GlobalTheory.BetaArchPf in
theorem betaArch_of_transport : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LBound → TorEx → BetaArch := by
  intro hTr hFD hLB hTE
  obtain ⟨CF1, hF1⟩ := hFD
  obtain ⟨CF2, hL2⟩ := hLB
  obtain ⟨CF3, hT3⟩ := hTE
  refine ⟨max CF1 (max CF2 CF3), fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, hF⟩ := hF1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, hL⟩ := hL2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C3, x3, hT⟩ := hT3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  obtain ⟨Cx, x4, hS⟩ := GlobalTheory.T.log_cmConstant_add_logDerivative_le_squareTopBound ε
  refine ⟨C2 + Cx, max (max x1 x2) (max x3 x4), fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => ?_⟩
  have hx1 : x1 ≤ large₂.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ large₂.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : x3 ≤ large₂.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : x4 ≤ large₂.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  intro i j s hs1 hs2 c y Λ hy hΛ
  obtain ⟨iCM, iAb, hFD, hbase, -⟩ := hF C1 le_rfl D large₂ hε hx1 hR T Lc μ₀ hμ G
  have TE := hT C3 le_rfl D large₂ hε hx3 hR T Lc μ₀ hμ G i j s hs1 hs2 c
  have LB := hL (C - Cx) (by linarith) D large₂ hε hx2 hR T Lc μ₀ hμ G i j s hs1 hs2
  have SZ := hS D large₂ hε hx4 hR i j s hs1 hs2

  obtain ⟨x, hxT, hx0, -, hxalg⟩ := TE
  have hyx : y = x := hy.2.unique hxT.2
  subst hyx
  have hd4 : 4 < D.host.d := hFD.2.1
  obtain ⟨K, hK2, hKd, φK, hφK, hc, hLat⟩ := GlobalTheory.T.exists_imagQuadratic_subfield_of_toricCMFieldData D.host.d (cmPhi D) hFD (host_d_mod' D) Λ hΛ
  obtain ⟨tt, 𝔞, Λσ, hσ, hEq, hAll⟩ := hTr K D.host.d hd4 hK2 hKd φK Λ hLat
  haveI := iCM
  haveI : IsGalois ℚ D.host.E := inferInstance
  have hU : UnramFin D.host.E := hFD.2.2.1
  have hCM : IsCMType (cmPhi D) := hFD.2.2.2.2.2.2.1
  have hcard : 2 ≤ Fintype.card D.what₂.Tau := hFD.2.2.2.2.2.1
  have hκ : ∀ τ, 1 ≤ kap D 1 i j s τ := fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D 1 i j τ hs2).2
  have hTF := hAll D.host.E hU D.what₂.Tau (cmPhi D) hcard hCM hφK s (kap D 1 i j s) (condF G.pl) hs1 hκ hbase
  have hVS : IsValSum (cmPhi D) s (kap D 1 i j s) (condF G.pl) ∅ (fam G μ₀ i j c) y :=
    ⟨fun _ h => absurd h (Finset.notMem_empty _), hy.1, (condQ_empty (condF G.pl)).symm ▸ hy.2⟩
  obtain ⟨halg, hconj⟩ := hTF.1 ∅ _ y hVS
  set M : ℕ := 2 * s * Fintype.card D.what₂.Tau + 2 * ∑ τ, kap D 1 i j s τ with hM
  set β := beta D.host.E D.host.d s (kap D 1 i j s) Λ y with hβ
  have hC0 : 0 < C0 D.host.E D.host.d (2 * s) (kap D 1 i j s) := cmValueConst_pos _ (by omega) (by omega) _
  have hβ0 : β ≠ 0 := by
    rw [hβ, beta_eq]
    exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (by exact_mod_cast hC0.ne') hx0)) (pow_ne_zero _ (latDisc_ne_zero _))
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by omega)
  let Fσ : (ℂ ≃+* ℂ) → ℝ := fun σ => 12 * Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) +
    12 * bTH D (C - Cx) large₂.sc.x large₂.sc.b -
      (M : ℝ) * Real.log (nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (Λσ σ)‖)
  have hFcl : ∀ σ σ', Fixes φK σ → Fixes φK σ' → ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') → Fσ σ = Fσ σ' := by
    intro σ σ' h h' hcl
    simp only [Fσ]
    rw [GlobalTheory.T.fractionalIdealNorm_pow_six_mul_discriminant_class_invariant φK hK2 hc (𝔞 σ) (𝔞 σ') (Λσ σ) (Λσ σ') (hσ σ h).2.1 (hσ σ' h').2.1 hcl]
  have hB : ∀ σ, Fixes φK σ → Real.log ‖σ β‖ ≤ Fσ σ := by
    intro σ hσf
    obtain ⟨π, χ', hw, hcc, hv'⟩ := GlobalTheory.T.exists_conjugate_cmValueCharacter_permuted_weight φK (cmPhi D) s (kap D 1 i j s) (condF G.pl) (fam G μ₀ i j c) σ
      hCM hφK hc hσf hy.1
    obtain ⟨Λ', hΛ'⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf D.host.E D.what₂.Tau (cmPhi D) _ χ' hCM hv'.1
      hv'.2.2.1 ⟨τ0, by have := hκ (π τ0); simp only [Function.comp]; omega⟩
    have hT' := toric_eq_L hU hCM hs1 hbase hv' hΛ'
    have hlog : Real.log ‖Λ' s‖ ≤ bTH D (C - Cx) large₂.sc.x large₂.sc.b := LB π χ' Λ' hv' hΛ'
    have h3 := ((hconj σ hσf (kap D 1 i j s ∘ π) hw χ' (Λ' s) ⟨hcc, hT'⟩).2)
    have hσβ : 0 < ‖σ β‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hβ0)
    have hn0 : 0 ≤ nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) := by
      unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
    have hN : 0 < nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (Λσ σ)‖ :=
      mul_pos (pow_pos (lt_of_le_of_ne hn0 (nrm_ne_zero _).symm) 6) (norm_pos_iff.2 (latDisc_ne_zero _))
    rw [h3] at hσβ ⊢
    have hA : 0 < C0 D.host.E D.host.d (2 * s) (kap D 1 i j s) * ‖Λ' s‖ := by
      rcases (mul_nonneg hC0.le (norm_nonneg (Λ' s))).lt_or_eq with h | h
      · exact h
      · rw [← h] at hσβ; simp at hσβ
    have hL0 : 0 < ‖Λ' s‖ := pos_of_mul_pos_right hA hC0.le
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv, Real.log_pow,
      Real.log_mul hC0.ne' hL0.ne']
    simp only [Fσ, hM]
    push_cast
    linarith
  obtain ⟨rep, hrep, hmain⟩ := GlobalTheory.T.mean_log_norm_conjugates_over_ideal_classes φK (jLat Λ) 𝔞 β Fσ hK2 hc hEq halg hβ0 hFcl hB
  have hmean := GlobalTheory.T.classMean_log_norm_disc_chowlaSelberg D φK hK2 hKd hd4 (fun c => 𝔞 (rep c)) (fun c => Λσ (rep c)) (fun c => (hrep c).2)
    (fun c => (hσ _ (hrep c).1).2.1)
  have hh : (0 : ℝ) < classNumber K := by
    rw [show (classNumber K : ℝ) = (Fintype.card (ClassGroup (𝓞 K)) : ℝ) from rfl]
    exact_mod_cast Fintype.card_pos
  have hsum : (∑ c, Fσ (rep c)) / classNumber K = 12 * Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) +
      12 * bTH D (C - Cx) large₂.sc.x large₂.sc.b - (M : ℝ) * ((∑ c, Real.log (nrm (𝔞 (rep c) : FractionalIdeal (𝓞 K)⁰ K) ^ 6 *
        ‖latDisc (Λσ (rep c))‖)) / classNumber K) := by
    simp only [Fσ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    rw [show (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = classNumber K from rfl]
    field_simp
  have hwt : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) = (M : ℝ) := by
    simp [hM, Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK]
  have hX : (∑ c, Fσ (rep c)) / classNumber K ≤ 12 * bTH D C large₂.sc.x large₂.sc.b := by
    rw [hsum, hmean, ← large₂.logDerivative_at_one_eq]
    have h2π : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
    have hγ : 0 ≤ Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
    have hMnn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hdl : large₂.logDerivativeAtOne ≤ |large₂.logDerivativeAtOne| := le_abs_self _
    have hbt : bTH D C large₂.sc.x large₂.sc.b = bTH D (C - Cx) large₂.sc.x large₂.sc.b + bTH D Cx large₂.sc.x large₂.sc.b := by
      unfold bTH; ring
    rw [hwt] at SZ
    nlinarith [mul_nonneg hMnn h2π.le, mul_nonneg hMnn hγ, mul_le_mul_of_nonneg_left hdl hMnn]
  calc _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg _)

end GlobalTheory.SqTop

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransportStatement

section

@[expose] public section

open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.betaConjugate_mean_logAbs_bound_of_transport : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LBound → TorEx → BetaArch := by
  first | exact @GlobalTheory.SqTop.betaArch_of_transport | exact GlobalTheory.SqTop.betaArch_of_transport | (intros; apply GlobalTheory.SqTop.betaArch_of_transport <;> assumption)
end
end
