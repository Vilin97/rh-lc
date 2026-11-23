module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemSpanOrderTwoRelationIffCoordsEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Mulvec
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.BdxLog
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.DetVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZKill
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsLinearEquivQuotientByOrderTwoCoords

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.exists_linearEquiv_quotientByOrderTwo_coords :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∃ e : Rq A c ε ≃ₗ[A] (Qc c → A), ∀ w : MonoidAlgebra A Γ, e (cls A c ε w) = coord c ε w := by
  intro A _ Γ _ _ c ε hc hc1 hε
  classical
  haveI : Fintype (Qc c) := Fintype.ofFinite (Qc c)
  let f : MonoidAlgebra A Γ →ₗ[A] (Qc c → A) :=
    { toFun := coord c ε
      map_add' := by
        intro x y
        funext i
        simp only [coord, MonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [coord, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
          RingHom.id_apply, Pi.smul_apply]
        ring }
  have hf : ∀ w, f w = coord c ε w := fun w => rfl
  have hker : LinearMap.ker f = (Ideal.span {rel A c ε}).restrictScalars A := by
    ext w
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_span_orderTwoRelation_iff_coords_eq_zero c ε hc hc1 hε, hf]
  have hrepinj : ∀ i i' : Qc c, rep i = rep i' → i = i' := by
    intro i i' h
    rw [← mk_rep i, ← mk_rep i', h]
  have hcrep : ∀ i i' : Qc c, rep i' ≠ c * rep i := by
    intro i i' h
    have e1 : i' = i := by
      rw [← mk_rep i', ← mk_rep i, h]
      exact ((mk_eq_mk hc (rep i) (c * rep i)).mpr (Or.inr rfl)).symm
    subst e1
    have e2 : c * rep i' = 1 * rep i' := by rw [← h, one_mul]
    exact hc1 (mul_right_cancel e2)
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨∑ i, MonoidAlgebra.single (rep i) (v i), ?_⟩
    funext i0
    rw [hf, coord]
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
    rw [Finset.sum_eq_single i0, Finset.sum_eq_zero]
    · simp
    · intro i _
      rw [if_neg (hcrep i0 i)]
    · intro i _ hi
      rw [if_neg (fun h => hi (hrepinj i i0 h))]
    · intro h
      exact absurd (Finset.mem_univ i0) h
  let e : Rq A c ε ≃ₗ[A] (Qc c → A) :=
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {rel A c ε})).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ f.quotKerEquivOfSurjective hsurj
  exact ⟨e, fun w => rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.AlgebraMapSignedInvolutionQuotientDetMemSpan

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.algebraMap_signedInvolutionQuotientDet_mem_span :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z : MonoidAlgebra A Γ, algebraMap A (MonoidAlgebra A Γ) (detR c ε z) ∈ Ideal.span {rel A c ε, z} := by
  intro A _ Γ _ _ c ε h1 h2 h3 z
  obtain ⟨e, he⟩ := UpperTheory.V.B5.exists_linearEquiv_quotientByOrderTwo_coords (A := A) c ε h1 h2 h3
  have hsc : ∀ (d : A) (w : MonoidAlgebra A Γ),
      coord c ε (algebraMap A (MonoidAlgebra A Γ) d * w) = d • coord c ε w := by
    intro d w
    funext i
    simp [coord, Algebra.algebraMap_eq_smul_one]
    ring
  obtain ⟨y, hy⟩ := e.surjective ((mat c ε z).adjugate.mulVec (coord c ε 1))
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hu : coord c ε u = (mat c ε z).adjugate.mulVec (coord c ε 1) := by
    rw [← he]
    exact hy
  have hcoord : coord c ε (z * u) = coord c ε (algebraMap A _ (detR c ε z) * 1) := by
    rw [UpperTheory.V.B5.coords_mul_eq_quotientMatrix_mulVec c ε h1 h2 h3, hu, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hsc,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [mul_one] at hcoord
  have hcls : cls A c ε (algebraMap A _ (detR c ε z)) = cls A c ε (z * u) := by
    apply e.injective
    rw [he, he, hcoord]
  have hmem : algebraMap A _ (detR c ε z) - z * u ∈ Ideal.span {rel A c ε} :=
    Ideal.Quotient.eq.mp hcls
  have hsub : Ideal.span {rel A c ε} ≤ Ideal.span {rel A c ε, z} :=
    Ideal.span_mono (by simp)
  have hz : z * u ∈ Ideal.span {rel A c ε, z} :=
    Ideal.mul_mem_right u _ (Ideal.subset_span (by simp))
  have := Ideal.add_mem _ (hsub hmem) hz
  simpa using this
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.AdjKill

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.adjKill :
    ∀ (A Γ X : Type) [CommRing A] [CommGroup Γ] [Finite Γ] [AddCommGroup X] [Module A X] (π : Representation A Γ X) (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ (z : MonoidAlgebra A Γ) (x : X), π c x = (ε : A) • x → π.asAlgebraHom z x = 0 → detR c ε z • x = 0 := by
  intro A Γ X _ _ _ _ _ π c ε hc hc1 hε z x hx hz
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (algebraMap_signedInvolutionQuotientDet_mem_span (A := A) c ε hc hc1 hε z)
  have hrel : π.asAlgebraHom (rel A c ε) x = 0 := by
    simp [rel, hx, Int.cast_smul_eq_zsmul]
  have key := congrArg (fun w => π.asAlgebraHom w x) hab
  simp only [map_add (f := _), map_mul, LinearMap.add_apply, Module.End.mul_apply, hrel, hz, map_zero,
    add_zero] at key
  rw [AlgHom.commutes, Module.algebraMap_end_apply] at key
  exact key.symm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.KillPow

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem nat_dvd_pow (l : ℕ) [hl : Fact l.Prime] (X : ℕ) (h0 : X ≠ 0) :
    ∃ r : ℕ, l ^ r ≤ X ∧ (X : ℤ_[l]) ∣ (l : ℤ_[l]) ^ r := by
  have hdvd : l ^ padicValNat l X ∣ X := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  refine ⟨padicValNat l X, Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd, ?_⟩
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := l) h0
    exact ⟨k, by rw [pow_succ, mul_assoc]; simpa [Nat.padicValNat_def] using hm⟩
  have hu : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hm0 (by simpa using h))
  have hX : (X : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l X * m := by
    conv_lhs => rw [hm]
    push_cast
    rfl
  rw [hX]
  simpa using mul_dvd_mul_left ((l : ℤ_[l]) ^ padicValNat l X) (hu.dvd (a := 1))

theorem UpperTheory.V.Odd.killPow :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), Procyc E Ω l → ∀ e : ℕ, 1 ≤ e → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ C * Module.finrank ℚ E * (e + 1) * Real.log ((e : ℝ) * l * N) ∧ ∀ x ∈ ShaMinus D e, (l : ℤ_[l]) ^ r • x = 0 := by
  obtain ⟨C, hC0, hC⟩ := bdxLog
  refine ⟨C, hC0, ?_⟩
  intro E Ω _ _ _ _ _ _ N hN hcyc l _ D hproc e he
  haveI : NeZero N := ⟨hN.ne'⟩
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hM0 : N * l ≠ 0 := Nat.mul_ne_zero hN.ne' (by omega)
  haveI : NeZero (N * l) := ⟨hM0⟩
  obtain ⟨ρ0, hρ0⟩ := actEx E Ω N hcyc
  have hNM : N ∣ N * l := dvd_mul_right N l
  have hρ := (actFacts E Ω N ρ0 hρ0).2.2.2.2 (N * l) hNM
  set ρ := ρ0.comp (ZMod.unitsMap hNM) with hρdef
  obtain ⟨_, _, hcard, _, _⟩ := actFacts E Ω (N * l) ρ hρ
  obtain ⟨hconj, hne⟩ := actConj E Ω (N * l) ρ hρ
  have hlM : l ∣ N * l := dvd_mul_left l N
  have hcop : (2 * (N * l) + 1).Coprime (N * l) := by
    simp [Nat.coprime_mul_left_add_left]
  have hodd : Odd (2 * (N * l) + 1) := odd_two_mul_add_one _
  obtain ⟨z, hzI, hzK⟩ := zKill E Ω l D e (N * l) ρ hρ he hproc hlM _ hcop hodd
  have hφs : Function.Surjective ⇑((piQ ρ)⁻¹) := by
    intro y
    obtain ⟨b, hb⟩ := piQ_surjective ρ y⁻¹
    exact ⟨b, by simp [hb]⟩
  have hφ1 : ((piQ ρ)⁻¹) (-1) ≠ 1 := by
    simpa using hne
  obtain ⟨r0, hr0, hdet⟩ := detVal l _ (N * l) _ e _ hcop hφs hφ1 he (by omega) z hzI
  have hT : Nat.totient (N * l) ≠ 0 := (Nat.totient_pos.mpr (NeZero.pos _)).ne'
  obtain ⟨r1, hr1le, hr1dvd⟩ := nat_dvd_pow l (Nat.totient (N * l)) hT
  refine ⟨r0 + r1, ?_, ?_⟩
  · have hb := hC N l e hN hl2 he
    have hr1 : (r1 : ℝ) * Real.log l ≤ Real.log ((N : ℝ) * l) := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast hr1le.trans (Nat.totient_le _)
    rw [hcard] at hr0
    have hd : (1 : ℝ) ≤ Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
    have hB := Real.log_natCast_nonneg (bdX (N * l) (2 * (N * l) + 1) (e + 1))
    have hL : 0 ≤ Real.log ((N : ℝ) * l) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      nlinarith)
    have h1 := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ Module.finrank ℚ E)
    have h2 := mul_nonneg (sub_nonneg.2 hd) hL
    push_cast
    nlinarith
  · intro x hx
    obtain ⟨hxS, hxE⟩ := Submodule.mem_inf.mp hx
    rw [Module.End.mem_eigenspace_iff] at hxE
    have hK := hzK x hxS
    have hcm : ((piQ ρ)⁻¹) (-1) = piQ ρ (-1) := by
      rw [MonoidHom.inv_apply, ← map_inv, inv_neg_one]
    have hc : (actRep D (e : ℤ) ρ (((piQ ρ)⁻¹) (-1))) (Nat.totient (N * l) • x)
        = (((-1) ^ (e + 1) : ℤ) : ℤ_[l]) • (Nat.totient (N * l) • x) := by
      rw [hcm, actRep_piQ, hconj, map_nsmul]
      change Nat.totient (N * l) • (cAct D (e : ℤ)) x = _
      rw [hxE, smul_comm]
      push_cast
      rfl
    have hcc : ((piQ ρ)⁻¹) (-1) * ((piQ ρ)⁻¹) (-1) = 1 := by
      rw [← map_mul]
      simp
    have hεε : ((-1) ^ (e + 1) : ℤ) * (-1) ^ (e + 1) = 1 := by
      rw [← mul_pow]
      simp
    have hkill := adjKill ℤ_[l] _ _ (actRep D (e : ℤ) ρ) _ _ hcc hφ1 hεε z _ hc hK
    obtain ⟨u, hu⟩ := hdet
    obtain ⟨v, hv⟩ := hr1dvd
    rw [pow_add, hu, hv]
    calc _ = (u * v) • (detR (((piQ ρ)⁻¹) (-1)) ((-1) ^ (e + 1)) z • (Nat.totient (N * l) • x)) := by
          rw [← Nat.cast_smul_eq_nsmul ℤ_[l], smul_smul, smul_smul]
          congr 1
          ring
      _ = 0 := by rw [hkill, smul_zero]
end
end
