module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExistsMaximal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitO
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitR
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitV

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitU

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section lin

variable {dim : (E →+* ℂ) → ℕ}

theorem IsU.add' {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim} (hu : IsU I x u)
    (hv : IsU I y v) : IsU I (x + y) (u + v) := by
  refine ⟨add_mem hu.1 hv.1, fun a ha => ?_⟩
  have hH : Hf (x + y) a = Hf x a + Hf y a := by
    simp [Hf, add_mul, Finset.sum_add_distrib]
  rw [inner_add_left, hu.2 a ha, hv.2 a ha, hH, Complex.add_im]

theorem IsU.zero' (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 := by
  exact ⟨zero_mem _, fun a _ => by simp [Hf]⟩

theorem IsU.zsmul' {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (k : ℤ) (hu : IsU I x u) :
    IsU I (k • x) (k • u) := by
  refine ⟨zsmul_mem hu.1 k, fun a ha => ?_⟩
  have hH : Hf (k • x) a = (k : ℂ) * Hf x a := by
    simp only [Hf]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_assoc]
  rw [← Int.cast_smul_eq_zsmul ℝ k u, real_inner_smul_left, hu.2 a ha, hH]
  simp

end lin

theorem eq_zero_of_im_L (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, (Hf y a).im = 0) : a = 0 := by
  have hH : ∀ y, Hf y a = inner ℂ a y := fun y => by
    simp [Hf, PiLp.inner_apply, mul_comm]
  have hf : (Complex.imLm.comp ((innerₛₗ ℂ a).restrictScalars ℝ) : Vsp X.dim →ₗ[ℝ] ℝ) = 0 :=
    X.b.ext fun i => by
      simpa [← hH] using h (X.b i) (Submodule.subset_span ⟨i, rfl⟩)
  have h0 : (inner ℂ a ((Complex.I : ℂ) • a)).im = 0 := by
    have := LinearMap.congr_fun hf ((Complex.I : ℂ) • a)
    first
      | exact this
      | (simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, innerₛₗ_apply,
          LinearMap.zero_apply] at this
         exact this)
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
  have h2 : ‖a‖ ^ 2 = 0 := by
    have h3 : (Complex.I * ((‖a‖ : ℂ) ^ 2)).im = ‖a‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [← h3]
    exact h0
  simpa using h2

theorem mem_L_of_int (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) :
    a ∈ X.L := by
  have hadd : ∀ y y' : Vsp X.dim, (Hf (y + y') a).im = (Hf y a).im + (Hf y' a).im :=
    fun y y' => by simp [Hf, add_mul, Finset.sum_add_distrib]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => (h (y : Vsp X.dim) y.2).choose
      map_zero' := by
        have e := (h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose_spec
        have e' : (((h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose : ℤ) : ℝ) = 0 := by
          rw [← e]
          simp [Hf]
        exact_mod_cast e'
      map_add' := fun y y' => by
        have e1 := (h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose_spec
        have e2 := (h (y : Vsp X.dim) y.2).choose_spec
        have e3 := (h (y' : Vsp X.dim) y'.2).choose_spec
        have e' : (((h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose : ℤ) : ℝ) =
            (h (y : Vsp X.dim) y.2).choose + (h (y' : Vsp X.dim) y'.2).choose := by
          rw [← e1, ← e2, ← e3, Submodule.coe_add, hadd]
        exact_mod_cast e' }
  obtain ⟨x, hx, hxy⟩ := X.perfect φ
  have key : a + x = 0 := by
    apply eq_zero_of_im_L X
    intro y hy
    have h1 : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf x y).im := hxy ⟨y, hy⟩
    have hφ : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf y a).im := (h y hy).choose_spec.symm
    have hc : (Hf y x).im = -(Hf x y).im := by
      have hcj : Hf y x = starRingEnd ℂ (Hf x y) := by simp [Hf, map_sum, mul_comm]
      rw [hcj, Complex.conj_im]
    have hr : Hf y (a + x) = Hf y a + Hf y x := by simp [Hf, mul_add, Finset.sum_add_distrib]
    rw [hr, Complex.add_im, hc, ← h1, hφ]
    ring
  have ha : a = -x := eq_neg_of_add_eq_zero_left key
  rw [ha]
  exact neg_mem hx

theorem exists_short_vectors_realSpan (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hsat : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) (hla : 0 < X.la1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧
      LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ Module.finrank ℝ (IR I) / X.la1 + ε := by
  set K := IR I with hK
  set N := Module.finrank ℝ K with hNdef
  let e : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) := (stdOrthonormalBasis ℝ K).repr
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin N)) :=
    { carrier := {z | ∃ y ∈ X.L, IsU I y ((e.symm z : K) : Vsp X.dim)}
      add_mem' := by
        rintro z z' ⟨y, hy, hu⟩ ⟨y', hy', hu'⟩
        exact ⟨y + y', X.L.add_mem hy hy', by simpa using hu.add' hu'⟩
      zero_mem' := ⟨0, X.L.zero_mem, by simpa using IsU.zero' I⟩
      smul_mem' := by
        rintro k z ⟨y, hy, hu⟩
        exact ⟨k • y, X.L.smul_mem k hy, by simpa using hu.zsmul' k⟩ }
  have hmemM : ∀ y ∈ X.L, ∀ u, IsU I y u → ∃ z ∈ M, ((e.symm z : K) : Vsp X.dim) = u :=
    fun y hy u hu => ⟨e ⟨u, hu.1⟩, ⟨y, hy, by simpa using hu⟩, by simp⟩
  have hinner : ∀ z z' : EuclideanSpace ℝ (Fin N),
      ⟪z, z'⟫_ℝ = ⟪((e.symm z : K) : Vsp X.dim), ((e.symm z' : K) : Vsp X.dim)⟫_ℝ := by
    intro z z'
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  have hnormE : ∀ z, ‖((e.symm z : K) : Vsp X.dim)‖ = ‖z‖ := by
    intro z
    rw [← e.symm.norm_map z]
    rfl
  have hdual : ∀ z ∈ PI.dualZ M, ((e.symm z : K) : Vsp X.dim) ∈ I := by
    intro z hz
    apply hsat _ ?_ (e.symm z).2
    apply mem_L_of_int X
    intro y hy
    obtain ⟨u, hu⟩ := exists_isU I y
    obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
    obtain ⟨k, hk⟩ := hz z' hz'M
    refine ⟨k, ?_⟩
    rw [← hu.2 _ (e.symm z).2, ← hk, hinner, hz', real_inner_comm]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have : IsEmpty (Fin N) := by rw [hN0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  obtain ⟨a0, ha0I, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hK0 : K = ⊥ := by
      rw [eq_bot_iff, hK]
      exact Submodule.span_le.2 (fun a ha => by simp [hcon a ha])
    have : N = 0 := by rw [hNdef, hK0]; exact finrank_bot ℝ _
    omega
  have hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro z hz
    have h0 : ∀ z' ∈ M, ⟪z', z⟫_ℝ = 0 := fun z' hz' =>
      (Submodule.mem_orthogonal _ _).1 hz z' (Submodule.subset_span hz')
    have ha : ((e.symm z : K) : Vsp X.dim) = 0 := by
      apply eq_zero_of_im_L X
      intro y hy
      obtain ⟨u, hu⟩ := exists_isU I y
      obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
      rw [← hu.2 _ (e.symm z).2, ← hz', ← hinner]
      exact h0 z' hz'M
    have : e.symm z = 0 := Subtype.ext ha
    simpa using congrArg e this

  obtain ⟨s, hsI, hsspan, hsli⟩ := exists_linearIndependent ℝ (I : Set (Vsp X.dim))
  have hsfin : s.Finite := hsli.setFinite
  set A := ∑ a ∈ hsfin.toFinset, ‖a‖ + 1 with hA
  have hApos : 0 < A := by
    have : 0 ≤ ∑ a ∈ hsfin.toFinset, ‖a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hlow : ∀ z ∈ M, z ≠ 0 → 1 / A ≤ ‖z‖ := by
    intro z hzM hz0
    obtain ⟨y, hy, hu⟩ := hzM
    set u := ((e.symm z : K) : Vsp X.dim)
    have hu0 : u ≠ 0 := by
      intro h0
      apply hz0
      have : e.symm z = 0 := Subtype.ext h0
      simpa using congrArg e this
    obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ⟪u, a⟫_ℝ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : ∀ w ∈ Submodule.span ℝ s, ⟪u, w⟫_ℝ = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx => exact hcon x hx
        | zero => exact inner_zero_right _
        | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
        | smul r x _ hx => rw [real_inner_smul_right, hx, mul_zero]
      have h1 := this u (by rw [hsspan]; exact hu.1)
      exact hu0 (inner_self_eq_zero.1 h1)
    have h1 : 1 ≤ |⟪u, a⟫_ℝ| := by
      rw [hu.2 a (mem_IR (hsI has))]
      rw [hu.2 a (mem_IR (hsI has))] at ha
      exact one_le_abs_im X hy (hle (hsI has)) ha
    have h2 : |⟪u, a⟫_ℝ| ≤ ‖u‖ * ‖a‖ := abs_real_inner_le_norm _ _
    have h3 : ‖a‖ ≤ A := by
      have := Finset.single_le_sum (f := fun a => ‖a‖) (fun _ _ => norm_nonneg _)
        ((Set.Finite.mem_toFinset hsfin).2 has)
      linarith
    rw [← hnormE z, div_le_iff₀ hApos]
    nlinarith [norm_nonneg u]
  have hdisc : DiscreteTopology M := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    refine ⟨1 / A, by positivity, fun z hz => ?_⟩
    by_contra hz0
    have h1 := hlow z z.2 (fun h => hz0 (Subtype.ext h))
    rw [dist_zero_right] at hz
    have : ‖(z : EuclideanSpace ℝ (Fin N))‖ = ‖z‖ := rfl
    linarith
  have hT := transference_successive_minima N M hdisc hspan N hNpos le_rfl
  rw [show N + 1 - N = 1 by omega] at hT
  have hsm0 : 0 ≤ PI.succMin M N := Real.sInf_nonneg (fun t ht => ht.1)
  have hdual1 : X.la1 ≤ PI.succMin (PI.dualZ M) 1 := by
    apply le_csInf
    · have hmem : e ⟨a0, mem_IR ha0I⟩ ∈ PI.dualZ M := by
        intro z hz
        obtain ⟨y, hy, hu⟩ := hz
        obtain ⟨k, hk⟩ := X.integral y a0 hy (hle ha0I)
        refine ⟨k, ?_⟩
        rw [hinner, LinearIsometryEquiv.symm_apply_apply, real_inner_comm, hu.2 a0 (mem_IR ha0I), hk]
      refine ⟨‖e ⟨a0, mem_IR ha0I⟩‖, norm_nonneg _, fun _ => e ⟨a0, mem_IR ha0I⟩,
        fun _ => hmem, ?_, fun _ => le_rfl⟩
      rw [linearIndependent_unique_iff]
      intro h0
      apply ha0
      have := congrArg e.symm h0
      simpa using congrArg Subtype.val this
    · rintro t ⟨-, v, hvM, hvli, hvt⟩
      have hv0 := hvli.ne_zero 0
      have ha := hdual (v 0) (hvM 0)
      have hne : ((e.symm (v 0) : K) : Vsp X.dim) ≠ 0 := by
        intro h0
        apply hv0
        have : e.symm (v 0) = 0 := Subtype.ext h0
        simpa using congrArg e this
      calc X.la1 ≤ ‖((e.symm (v 0) : K) : Vsp X.dim)‖ := sq_le_Qy_of_le_firstMinimum X (hle ha) hne
        _ = ‖v 0‖ := hnormE _
        _ ≤ t := hvt 0
  have hlam : PI.succMin M N ≤ N / X.la1 := by
    rw [le_div_iff₀ hla]
    nlinarith

  have hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty := by
    obtain ⟨s', hs'M, hs'span, hs'li⟩ := exists_linearIndependent ℝ (M : Set (EuclideanSpace ℝ (Fin N)))
    have hfin' : s'.Finite := hs'li.setFinite
    have : Fintype s' := hfin'.fintype
    let bs := Module.Basis.mk hs'li (by rw [Subtype.range_coe, hs'span, hspan])
    have hcard : Fintype.card s' = N := by
      rw [← Module.finrank_eq_card_basis bs, finrank_euclideanSpace_fin]
    let eq : Fin N ≃ s' := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨∑ j, ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖,
      Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun j => (eq j : EuclideanSpace ℝ (Fin N)),
      fun j => hs'M (eq j).2, hs'li.comp eq eq.injective, fun j => ?_⟩
    exact Finset.single_le_sum (f := fun j => ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨t, ⟨-, v, hvM, hvli, hvt⟩, htlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (PI.succMin M N) hε)
  choose y hy hyU using hvM
  refine ⟨y, fun j => ((e.symm (v j) : K) : Vsp X.dim), fun j => ⟨hy j, hyU j⟩, ?_, ?_⟩
  · exact (hvli.map' e.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)).map' K.subtype
      K.ker_subtype
  · intro j
    rw [hnormE]
    have := hvt j
    have h2 : PI.succMin M N = sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t} := rfl
    linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitG

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem IR_bot {dim : (E →+* ℂ) → ℕ} : IR (⊥ : Submodule ℤ (Vsp dim)) = ⊥ := by
  simp [IR]

theorem split_bot (X : PT E) {DF : ℕ} (P : Par X DF) (h : ¬ X.la1 < P.th) : IsSplit P ⊥ := by
  have hIR : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := IR_bot
  have h0 : Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))) = 0 := by
    rw [hIR]; exact finrank_bot ℝ (Vsp X.dim)
  have h' : ¬ X.la1 < th (E := E) P.q P.R0 := h
  have hph : P.ph = 0 := by
    unfold Par.ph PT.ph
    rw [if_neg h']
  refine
    { le := bot_le
      sat := ?_
      stable := ?_
      iso := ?_
      eps := ?_
      rank := ⟨0, Nat.zero_le _, by rw [h0, mul_zero]⟩
      ne_bot := iff_of_false (fun h'' => h'' rfl) h
      thick := ?_
      sep := ?_
      u1 := ?_
      u2 := ?_ }
  · intro x _ k hk hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [← Int.cast_smul_eq_zsmul ℂ] at hx
    exact (smul_eq_zero.mp hx).resolve_left (by exact_mod_cast hk)
  · intro α x hx
    rw [Submodule.mem_bot] at hx ⊢
    subst hx
    ext i
    simp [act]
  · intro x hx y hy
    rw [Submodule.mem_bot] at hx hy
    subst hx hy
    simp [Hf]
  · intro x hx
    rw [Submodule.mem_bot] at hx
    subst hx
    exact X.eps_iso 0 (Submodule.zero_mem _) (fun α => by simp [Hf])
  · intro x hxL _ hx
    rw [Submodule.mem_bot] at hx
    rw [hIR]
    have hinf : Metric.infDist x ((⊥ : Submodule ℝ (Vsp X.dim)) : Set (Vsp X.dim)) = ‖x‖ := by
      rw [Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]
    rw [hinf]
    have hle : X.la1 ≤ ‖x‖ := by
      unfold PT.la1
      apply csInf_le
      · exact ⟨0, fun t ⟨y, _, _, ht⟩ => by rw [ht]; exact norm_nonneg y⟩
      · exact ⟨x, hxL, hx, rfl⟩
    exact (not_lt.mp h).trans hle
  · intro x _ u hu hu0
    exfalso
    apply hu0
    unfold IsU at hu
    have hu1 := hu.1
    rw [hIR, Submodule.mem_bot] at hu1
    exact hu1
  · haveI : IsEmpty (Fin (Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))))) := by
      rw [h0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  · intro k x u _ _
    rw [hph]
    exact Finset.sum_nonneg fun j _ => by positivity

theorem le_of_forall_pos_div_sq {a c S : ℝ} (ha : 0 < a) (hc : 0 < c) (h : ∀ ε > 0, c / (a + ε) ^ 2 ≤ S) :
    c / a ^ 2 ≤ S := by
  have hcont : ContinuousAt (fun ε : ℝ => c / (a + ε) ^ 2) 0 := by
    apply ContinuousAt.div continuousAt_const
    · exact ((continuous_const.add continuous_id).pow 2).continuousAt
    · simpa using ha.ne'
  have ht : Filter.Tendsto (fun ε : ℝ => c / (a + ε) ^ 2) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (c / a ^ 2)) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε using h ε hε

theorem sq_le_pow_four_div_sq {d N la u : ℝ} (hd : 2 ≤ d) (hN : N ≤ d) (hla : 0 < la) (hu0 : 0 ≤ u)
    (hu : u ≤ N / la + 1 / la) : u ^ 2 ≤ d ^ 4 / la ^ 2 := by
  have key : u * la ≤ N + 1 := by
    have e : N / la + 1 / la = (N + 1) / la := by ring
    rw [e] at hu
    have e2 : (N + 1) / la * la = N + 1 := by field_simp
    calc u * la ≤ (N + 1) / la * la := mul_le_mul_of_nonneg_right hu hla.le
      _ = N + 1 := e2
  have hla2 : 0 < la ^ 2 := by positivity
  rw [le_div_iff₀ hla2]
  have h2 : u * la ≤ d ^ 2 := by nlinarith
  have h3 : 0 ≤ u * la := mul_nonneg hu0 hla.le
  nlinarith [mul_le_mul h2 h2 h3 (by positivity : (0:ℝ) ≤ d ^ 2)]

theorem split_pos (X : PT E) {DF : ℕ} (P : Par X DF) (h : X.la1 < P.th) : ∃ I, IsSplit P I := by
  obtain ⟨n, ω, hω, hsp⟩ := omega_exists' (E := E)
  have hf1n : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have hf1 : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1n
  have hrd := P.hrd
  have hRR : (0 : ℝ) < RR (E := E) := by rw [RR]; positivity
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hR0 : (0 : ℝ) < P.R0 ^ 2 := by linarith [P.hR0.1]
  set Ω := omStar (E := E) with hΩdef
  have hΩ : 0 < Ω := by rw [hΩdef, omStar]; positivity
  have hΩ2 : Ω ^ 2 = 4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2 := by
    rw [hΩdef, omStar, mul_pow, mul_pow, ← Real.rpow_natCast ((PT.f E : ℝ) ^ ((3 : ℝ) / 2)),
      ← Real.rpow_mul (by positivity)]
    norm_num
  have hth2 : P.th ^ 2 = PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 / P.q := by
    rw [Par.th, th, Real.sq_sqrt]; positivity
  have hth : 0 < P.th := by
    rw [Par.th, th]; apply Real.sqrt_pos.2; positivity
  have hd2n : 2 ≤ dstar (E := E) P.m := by
    rw [dstar]; have := P.hm1; nlinarith
  have hd2 : (2 : ℝ) ≤ dstar (E := E) P.m := by exact_mod_cast hd2n
  have hC1 : (dstar (E := E) P.m : ℝ) ^ 2 * Ω * P.th ^ 2 < 1 := P.C1
  have hΩth : Ω * P.th ^ 2 ≤ 1 := by nlinarith [sq_nonneg P.th, hΩ]
  obtain ⟨I, hI, hmax⟩ := exists_maximal X ω hΩ hth hΩth hω hsp
  obtain ⟨τ, hτ⟩ := P.hm
  have hr : 1 ≤ X.r := by
    have := P.hfr
    rcases Nat.eq_zero_or_pos X.r with h0 | h0
    · rw [h0] at this; simp at this
    · exact h0
  have hne := L_ne_zero X hr τ
  have hla := first_minimum_pos X hne
  have h' : X.la1 < th (E := E) P.q P.R0 := h
  have hph : P.ph = 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) := by rw [Par.ph, PT.ph, if_pos h']
  obtain ⟨ρ, hρ, hfr⟩ := rank_iso X I hI.le hI.stable hI.iso
  have hin : ∀ x ∈ X.L, ‖x‖ < P.th → x ∈ I := by
    intro x hx hxs
    by_contra hxI
    have h1 := hmax x hx hxI
    have h2 : Metric.infDist x (IR I) ≤ ‖x‖ := by
      rw [← dist_zero_right]; exact Metric.infDist_le_dist_of_mem (IR I).zero_mem
    linarith
  refine ⟨I, hI.le, sat_of_IR hI.sat, hI.stable, hI.iso, ?_, ⟨ρ, le_trans (hρ τ) hτ, hfr⟩, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact X.eps_iso x (hI.le hx) (fun α => hI.iso _ (hI.stable α x hx) x hx)
  · refine ⟨fun _ => h, fun _ hbot => ?_⟩
    obtain ⟨x, hx, hx0, hxs⟩ := exists_short X hne h
    have := hin x hx hxs
    rw [hbot, Submodule.mem_bot] at this
    exact hx0 this
  · intro x hx _ hxI
    exact hmax x hx hxI
  · intro x hx u hu hne
    have h1 := hI.sep x hx u hu hne
    have key : b0 (E := E) P.q P.R0 * (Ω ^ 2 * P.th ^ 2) = 4 * (PT.f E : ℝ) ^ 4 * PT.rd E ^ 2 / RR (E := E) := by
      have hR0ne : P.R0 ≠ 0 := fun h0 => by rw [h0] at hR0; simp at hR0
      rw [hΩ2, hth2, b0]; field_simp
    have hf4 : (PT.f E : ℝ) ^ 4 ≤ PT.rd E ^ 2 := by
      have := P.hf2
      calc (PT.f E : ℝ) ^ 4 = ((PT.f E : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ PT.rd E ^ 2 := pow_le_pow_left₀ (by positivity) this 2
    have hb : b0 (E := E) P.q P.R0 * (Ω ^ 2 * P.th ^ 2) ≤ 1 := by
      rw [key, div_le_one hRR, RR]
      have : 4 * PT.rd E ^ 4 ≤ PT.rd E ^ 7 := by
        have h3 : (4 : ℝ) ≤ PT.rd E ^ 3 := by nlinarith
        calc 4 * PT.rd E ^ 4 ≤ PT.rd E ^ 3 * PT.rd E ^ 4 :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = PT.rd E ^ 7 := by ring
      nlinarith [pow_pos (show (0:ℝ) < PT.rd E by linarith) 2]
    have hb' : b0 (E := E) P.q P.R0 ≤ (1 / (Ω * P.th)) ^ 2 := by
      rw [div_pow, one_pow, mul_pow, le_div_iff₀ (by positivity)]
      exact hb
    exact hb'.trans (pow_le_pow_left₀ (by positivity) h1.le 2)
  · obtain ⟨x, u, hxu, hli, hb⟩ := exists_short_vectors_realSpan X I hI.le hI.sat hla (ε := 1 / X.la1) (by positivity)
    refine ⟨x, u, hxu, hli, fun j => ?_⟩
    have hN : (Module.finrank ℝ (IR I) : ℝ) ≤ dstar (E := E) P.m := by
      have : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
        rw [hfr, dstar]; exact Nat.mul_le_mul_left _ (le_trans (hρ τ) hτ)
      exact_mod_cast this
    set d : ℝ := (dstar (E := E) P.m : ℝ)
    have hR : PT.rd E ^ 2 * d ^ 4 * P.ph / (2 * PT.f E) = d ^ 4 / X.la1 ^ 2 := by
      rw [hph]; field_simp
    rw [hR]
    exact sq_le_pow_four_div_sq hd2 hN hla (norm_nonneg _) (hb j)
  · intro k x u hxu hspan
    rw [hph]
    set S := ∑ j, ‖u j‖ ^ 2 / 2
    set c : ℝ := 2 * PT.f E / PT.rd E ^ 2 with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hbound : ∀ ε > 0, c / (X.la1 + ε) ^ 2 ≤ S := by
      intro ε hε
      obtain ⟨ξ, hξ, hξ0, hξs⟩ := exists_short X hne (lt_min h (by linarith : X.la1 < X.la1 + ε))
      have hξI := hin ξ hξ (lt_of_lt_of_le hξs (min_le_left _ _))
      have h1 := sum_sq_norm_ge_of_span X I hI.le hI.stable hξI hξ0 k x u hxu hspan
      have h2 : c / (X.la1 + ε) ^ 2 ≤ c / ‖ξ‖ ^ 2 := by
        apply div_le_div_of_nonneg_left hcpos.le (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (lt_of_lt_of_le hξs (min_le_right _ _))) 2
      refine h2.trans (le_of_eq_of_le ?_ h1)
      rw [hc]; field_simp
    have hl := le_of_forall_pos_div_sq hla hcpos hbound
    calc 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) = c / X.la1 ^ 2 := by rw [hc]; field_simp
      _ ≤ S := hl

end

end ReciprocityTheory.ChartRestriction.G.I2
end
end
