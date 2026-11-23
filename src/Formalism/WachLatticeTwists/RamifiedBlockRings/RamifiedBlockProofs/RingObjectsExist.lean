module

public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdemFactor
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.Ideal.BigOperators
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RingObjectsOfMatrixData
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.SplitFibre
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdemKO

section

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem idemKO : StatIdemKO := by
  intro O _ _ _ n _ _ e he hr
  classical
  set eK := e.map (algebraMap O (FractionRing O)) with heK
  have hidK : eK * eK = eK := by
    rw [heK, ← Matrix.map_mul, he]
  have hsub : (LinearMap.range (Matrix.toLin' eK)).subtype.comp (Matrix.toLin' eK).rangeRestrict =
      Matrix.toLin' eK := LinearMap.ext fun v => rfl
  have hid : (Matrix.toLin' eK).rangeRestrict.comp (LinearMap.range (Matrix.toLin' eK)).subtype =
      LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨v, w, rfl⟩
    apply Subtype.ext
    show Matrix.toLin' eK (Matrix.toLin' eK w) = Matrix.toLin' eK w
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hidK]
  have hfr : Module.finrank (FractionRing O) (LinearMap.range (Matrix.toLin' eK)) = 1 := by
    rw [← hr]
    exact Matrix.finrank_range_mulVecLin eK
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 1) (FractionRing O) (LinearMap.range (Matrix.toLin' eK))) :=
    ⟨Module.finBasisOfFinrankEq _ _ hfr⟩
  obtain ⟨U, W, hUW, hWU⟩ : ∃ (U : Matrix n (Fin 1) (FractionRing O))
      (W : Matrix (Fin 1) n (FractionRing O)), U * W = eK ∧ W * U = 1 :=
    ⟨LinearMap.toMatrix b (Pi.basisFun _ n) (LinearMap.range (Matrix.toLin' eK)).subtype,
      LinearMap.toMatrix (Pi.basisFun _ n) b (Matrix.toLin' eK).rangeRestrict,
      by rw [← LinearMap.toMatrix_comp, hsub, LinearMap.toMatrix_eq_toMatrix',
        LinearMap.toMatrix'_toLin'],
      by rw [← LinearMap.toMatrix_comp, hid, LinearMap.toMatrix_id]⟩
  have hfact : ∀ i j, eK i j = U i 0 * W 0 j := by
    intro i j
    rw [← hUW, Matrix.mul_apply, Fin.sum_univ_one]
  have hsum : ∑ i, W 0 i * U i 0 = 1 := by
    have h := congrFun (congrFun hWU 0) 0
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have inj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have hmap : ∀ i j, algebraMap O (FractionRing O) (e i j) = eK i j := fun i j => rfl
  have htr : ∑ i, e i i = 1 := by
    apply inj

    rw [map_sum, map_one]
    simp only [hmap, hfact]
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨i0, hi0⟩ : ∃ i0, IsUnit (e i0 i0) := by
    by_contra hcon
    push_neg at hcon
    have hmem : ∑ i, e i i ∈ IsLocalRing.maximalIdeal O :=
      Ideal.sum_mem _ fun i _ => (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (hcon i))
    rw [htr] at hmem
    exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hmem) isUnit_one
  have hminor : ∀ i j k l, e i j * e k l = e i l * e k j := by
    intro i j k l
    apply inj
    simp only [map_mul, hmap, hfact]
    ring
  obtain ⟨c, hc⟩ := hi0
  have hfe : ∀ i j, e i j = e i i0 * (↑c⁻¹ * e i0 j) := by
    intro i j
    have h := hminor i j i0 i0
    rw [← hc] at h
    calc e i j = e i j * ↑c * ↑c⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h]; ring
  have hφu : ∑ j, ↑c⁻¹ * e i0 j * e j i0 = 1 := by
    have h := congrFun (congrFun he i0) i0
    rw [Matrix.mul_apply, ← hc] at h
    calc ∑ j, ↑c⁻¹ * e i0 j * e j i0 = ↑c⁻¹ * ∑ j, e i0 j * e j i0 := by
          rw [Finset.mul_sum]
          simp only [mul_assoc]
      _ = 1 := by rw [h, Units.inv_mul]
  let ψ : KO O →ₗ[O] (n → KO O) := LinearMap.pi fun i => e i i0 • LinearMap.id
  let χ : (n → KO O) →ₗ[O] KO O := ∑ j, (↑c⁻¹ * e i0 j) • LinearMap.proj j
  have hχψ : ∀ m, χ (ψ m) = m := by
    intro m
    simp only [χ, ψ, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, LinearMap.pi_apply, LinearMap.id_apply, smul_smul]
    rw [← Finset.sum_smul, hφu, one_smul]
  have hmat : matEnd O (KO O) n e = ψ.comp χ := by
    apply LinearMap.ext
    intro v
    funext i
    show ∑ j, e i j • v j = _
    simp only [χ, ψ, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.sum_apply, LinearMap.proj_apply,
      Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [hfe i j]
  have hinj : Function.Injective ψ := fun a b h => by rw [← hχψ a, ← hχψ b, h]
  have hχ : LinearMap.range χ = ⊤ := LinearMap.range_eq_top.2 fun m => ⟨ψ m, hχψ m⟩
  exact ⟨(LinearEquiv.ofEq _ _ (by rw [hmat, LinearMap.range_comp_of_range_eq_top ψ hχ])).trans
    (LinearEquiv.ofInjective ψ hinj).symm⟩

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end
end

-- Source module: Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.SplitPts

section

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities


theorem splitPts : StatSplitPts := by
  intro O _ _ Xs T t P hPc hPr
  rcases isEmpty_or_nonempty Xs with hX | hX
  · exact ⟨fun _ _ => 0, fun _ => (splitT T t P).zero_mem, fun f' _ => ⟨fun _ _ => 0, fun _ => T.zero_mem,
      funext fun y => (hX.elim y.1.1)⟩, fun x => hX.elim x⟩
  have hnt : Nontrivial T := inferInstance
  let evT : Xs → (T →+* O) := fun x => (Pi.evalRingHom (fun _ : Xs => O) x).comp T.val.toRingHom
  have hmonP : ∀ x, (P x).Monic := fun x => by
    obtain ⟨α, -, h⟩ := hPr x
    rw [h]; exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdegP : ∀ x, (P x).natDegree = t := fun x => by
    obtain ⟨α, -, h⟩ := hPr x
    rw [h, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]; simp
  let PT : Polynomial T := ∑ k ∈ range (t + 1), Polynomial.monomial k ⟨fun x => (P x).coeff k, hPc k⟩
  have hcoef : ∀ k, PT.coeff k = if k ≤ t then ⟨fun x => (P x).coeff k, hPc k⟩ else 0 := by
    intro k
    simp only [PT, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Finset.sum_ite_eq',
      Finset.mem_range, Nat.lt_succ_iff]
  have hmap : ∀ x, PT.map (evT x) = P x := by
    intro x
    ext k
    rw [Polynomial.coeff_map, hcoef]
    split_ifs with hk
    · rfl
    · rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegP]; omega)]
  have hle : PT.natDegree ≤ t := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hcoef, if_neg (by omega)]
  have hone : PT.coeff t = 1 := by
    rw [hcoef, if_pos le_rfl]
    refine Subtype.ext (funext fun x => ?_)
    have := (hmonP x).coeff_natDegree
    rw [hdegP] at this
    exact this
  have hmon : PT.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one t hle hone
  have hdeg : PT.natDegree = t :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (by rw [hone]; exact one_ne_zero))
  have key := splitAlg T PT hmon
  rw [hdeg] at key
  obtain ⟨T', _, _, rr, hfree, hfin, hrank, hfac, hadj, huniv⟩ := key
  have hψ : ∀ y : SplitPts t P, ∃ ψ : T' →+* O, ψ.comp (algebraMap T T') = evT y.1.1 ∧
      ∀ i, ψ (rr i) = y.1.2 i := by
    intro y
    letI : Algebra T O := (evT y.1.1).toAlgebra
    obtain ⟨φ, hφ, -⟩ := huniv O y.1.2 (by
      show PT.map (evT y.1.1) = _
      rw [hmap]; exact y.2)
    exact ⟨φ.toRingHom, RingHom.ext fun τ => φ.commutes τ, hφ⟩
  choose ψ hψ1 hψ2 using hψ
  let Ψ : T' →+* (SplitPts t P → O) := Pi.ringHom ψ
  let bas : Module.Basis (Fin t.factorial) T T' := Module.finBasisOfFinrankEq T T' hrank
  have hΨa : ∀ τ : T, Ψ (algebraMap T T' τ) = fun y => τ.1 y.1.1 :=
    fun τ => funext fun y => RingHom.congr_fun (hψ1 y) τ
  have hrange : ∀ f' ∈ splitT T t P, ∃ z, Ψ z = f' := by
    intro f' hf'
    induction hf' using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨f, hf, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨algebraMap T T' ⟨f, hf⟩, hΨa _⟩
      · exact ⟨rr i, funext fun y => hψ2 y i⟩
    | algebraMap c => exact ⟨algebraMap T T' (algebraMap O T c), hΨa _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩
  have hmemΨ : ∀ z, Ψ z ∈ splitT T t P := by
    intro z
    have hz : z ∈ Algebra.adjoin T (Set.range rr) := hadj ▸ Algebra.mem_top
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have h1 : Ψ (rr i) = splitRoot t P i := funext fun y => hψ2 y i
      rw [h1]
      exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
    | algebraMap τ =>
      rw [hΨa]
      exact Algebra.subset_adjoin (Or.inl ⟨τ.1, τ.2, rfl⟩)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨fun k => Ψ (bas k), fun k => hmemΨ _, ?_, ?_⟩
  · intro f' hf'
    obtain ⟨z, rfl⟩ := hrange f' hf'
    refine ⟨fun k => (bas.repr z k).1, fun k => (bas.repr z k).2, ?_⟩
    conv_lhs => rw [← bas.sum_repr z]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hΨa]
  · intro x a ha
    let K := FractionRing O
    let ι : O →+* K := algebraMap O K
    have hι : Function.Injective ι := IsFractionRing.injective O K
    obtain ⟨α, hα, hPα⟩ := hPr x
    have hmapK : PT.map (ι.comp (evT x)) = ∏ i, (Polynomial.X - Polynomial.C (ι (α i))) := by
      rw [← Polynomial.map_map, hmap, hPα, Polynomial.map_prod]; simp
    have sf := splitFibre T T' K PT hmon
    rw [hdeg] at sf
    have hz := sf rr hfac hadj bas (ι.comp (evT x)) (fun i => ι (α i)) (hι.comp hα) hmapK
      (fun k => ι (a k)) (by
      intro φ hφ
      have h1 : ∏ i, (Polynomial.X - Polynomial.C (φ (rr i))) =
          ∏ i, (Polynomial.X - Polynomial.C (ι (α i))) := by
        rw [← hmapK, ← hφ, ← Polynomial.map_map, hfac, Polynomial.map_prod]; simp
      have h2 : ∀ i, ∃ j, φ (rr i) = ι (α j) := by
        intro i
        have h3 : (∏ j, (Polynomial.X - Polynomial.C (ι (α j)))).eval (φ (rr i)) = 0 := by
          rw [← h1, Polynomial.eval_prod]
          exact Finset.prod_eq_zero (mem_univ i) (by simp)
        rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h3
        obtain ⟨j, -, hj⟩ := h3
        exact ⟨j, by simpa [sub_eq_zero] using hj⟩
      choose σ hσ using h2
      have hy : P x = ∏ i, (Polynomial.X - Polynomial.C (α (σ i))) := by
        apply Polynomial.map_injective ι hι
        rw [hPα, Polynomial.map_prod, Polynomial.map_prod]
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        rw [← h1]
        exact Finset.prod_congr rfl fun i _ => by rw [hσ]
      let y : SplitPts t P := ⟨(x, fun i => α (σ i)), hy⟩
      have hφy : ∀ z, φ z = ι (ψ y z) := by
        letI : Algebra T K := (ι.comp (evT x)).toAlgebra
        let φ1 : T' →ₐ[T] K := { φ with commutes' := fun τ => RingHom.congr_fun hφ τ }
        let φ2 : T' →ₐ[T] K :=
          { (ι.comp (ψ y)) with
            commutes' := fun τ => by
              show ι (ψ y (algebraMap T T' τ)) = _
              rw [show ψ y (algebraMap T T' τ) = evT x τ from RingHom.congr_fun (hψ1 y) τ]
              rfl }
        have h12 : φ1 = φ2 := AlgHom.ext_of_adjoin_eq_top hadj (by
          rintro _ ⟨i, rfl⟩
          show φ (rr i) = ι (ψ y (rr i))
          rw [hψ2, hσ])
        exact fun z => DFunLike.congr_fun h12 z
      have h4 := congrArg ι (ha y rfl)

      rw [map_sum, map_zero] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hφy, map_mul]
      rfl)
    funext k
    exact hι (by
      show ι (a k) = ι 0
      rw [map_zero]; exact congrFun hz k)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end
end

-- Source module: Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RingObjectsExist

section

@[expose] public section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

theorem ring_objects_exist : RingObjectsExist := ring_objects_of_matrix_data eMat splitPts idemKO

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end
