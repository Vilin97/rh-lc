module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChart
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChartPointTrdeg
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsDerivSpanTrdeg
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFreeParAlgIndep
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenericFormsKer
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecPointSeparable
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfChartPointSecPointSpecChart
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsAlt
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
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsDerivSpanTrdeg
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Kaehler.Basic
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecSeparable
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenericFormsKer
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecPointSeparable
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChart

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartPointTrdeg

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem ChartPointTrdeg.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : AffineChartTrdeg.Statement) :
    ChartPointTrdeg.Statement := by
  intro k L _ _ _ n e Q g hQ hg x j₀ hx hj
  have := hQ.isPrime
  have hdim := h₁ k n (e + 1) Q g hQ hg
  have hXj : (X j₀ : MvPolynomial (Fin n) k) ∉ Q := fun h => hj (by simpa using hx _ h)
  have htr := h₂ k n e Q j₀ hQ hdim hXj
  let R := MvPolynomial (Fin n) k ⧸ Q
  let K := FractionRing R
  let π : R →ₐ[k] L := Ideal.Quotient.liftₐ Q (aeval x) hx
  let s : R := Ideal.Quotient.mk Q (X j₀)
  have hs : s ≠ 0 := by
    intro h
    exact hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hπX : ∀ m, π (Ideal.Quotient.mk Q (X m)) = x m := fun m =>
    (AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp Q (aeval x) hx) (X m)).trans (aeval_X x m)
  have hπs : π s = x j₀ := hπX j₀
  have hπu : IsUnit (π s) := by rw [hπs]; exact hj.isUnit
  have hKs : algebraMap R K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs
  let S := Localization.Away s
  let ρ : S →ₐ[k] L := IsLocalization.Away.liftAlgHom s hπu
  let ι : S →ₐ[k] K :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom k R K) s hKs.isUnit
  have hSinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hι : Function.Injective ι := by
    show Function.Injective (IsLocalization.Away.lift (g := algebraMap R K) s hKs.isUnit)
    refine (IsLocalization.lift_injective_iff _).mpr fun a b => ?_
    rw [hSinj.eq_iff, (IsFractionRing.injective R K).eq_iff]
  let y : Fin n → S := fun m => algebraMap R S (Ideal.Quotient.mk Q (X m)) * IsLocalization.Away.invSelf s
  have hinv : ∀ {B : Type} [Field B] [Algebra k B] (φ : S →ₐ[k] B),
      φ (IsLocalization.Away.invSelf s) = (φ (algebraMap R S s))⁻¹ := by
    intro B _ _ φ
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hιR : ∀ a, ι (algebraMap R S a) = algebraMap R K a := fun a =>
    IsLocalization.Away.lift_eq (g := algebraMap R K) s hKs.isUnit a
  have hρR : ∀ a, ρ (algebraMap R S a) = π a := fun a =>
    IsLocalization.Away.lift_eq (g := (π : R →+* L)) s hπu a
  have hιy : ι ∘ y = fun m => genPt Q m * (genPt Q j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ι, hιR]
    rfl
  have hρy : ρ ∘ y = fun m => x m * (x j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ρ, hρR, hπX, s]
  let T := Algebra.adjoin k (Set.range y)
  have hA : T.map ι = Algebra.adjoin k (Set.range fun m => genPt Q m * (genPt Q j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hιy]
  have hB : T.map ρ = Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hρy]
  have hTA : Algebra.trdeg k T = Algebra.trdeg k (T.map ι) :=
    (Subalgebra.equivMapOfInjective T ι hι).trdeg_eq
  have hBT : Algebra.trdeg k (T.map ρ) ≤ Algebra.trdeg k T := by
    refine trdeg_le_of_surjective ((ρ.comp T.val).codRestrict (T.map ρ)
      (fun t => ⟨t, t.2, rfl⟩)) ?_
    rintro ⟨b, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  rw [← hB]
  rw [hA, htr] at hTA
  exact hBT.trans hTA.le

end

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PDerivSpanTrdeg

section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin

theorem DerivSpanTrdeg.derivation_eq_zero_of_isSeparable {k K M : Type*} [Field k] [Field K]
    [Algebra k K] [AddCommGroup M] [Module K M] [Module k M] [IsScalarTower k K M] (s : Set K)
    [Algebra.IsSeparable (IntermediateField.adjoin k s) K] (D : Derivation k K M)
    (hs : ∀ x ∈ s, D x = 0) : D = 0 := by
  have hE : ∀ x ∈ IntermediateField.adjoin k s, D x = 0 := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap x => exact D.map_algebraMap x
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | inv x _ hx => rw [Derivation.leibniz_inv, hx, smul_zero]
    | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  ext α
  set E := IntermediateField.adjoin k s
  have hsep : IsSeparable E α := Algebra.IsSeparable.isSeparable E α
  set g : Polynomial K := (minpoly E α).map (algebraMap E K)
  have h0 : D (g.eval α) = 0 := by
    rw [Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  have hc : D.mapCoeffs g = 0 := by
    ext i
    simp only [Derivation.mapCoeffs_apply, g, Polynomial.coeff_map]
    exact (hE _ ((minpoly E α).coeff i).2).trans (by simp)
  rw [Derivation.apply_eval_eq, hc, map_zero, zero_add] at h0
  have hne : g.derivative.eval α ≠ 0 := by
    simp only [g]
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval E α)
  simpa [hne] using h0

theorem DerivSpanTrdeg.proof : DerivSpanTrdeg.Statement := by
  intro k L _ _ _ _ ι _ z e he
  classical
  set F₀ := IntermediateField.adjoin k (Set.range z)
  have : Algebra.EssFiniteType k F₀ := by
    rw [IntermediateField.essFiniteType_iff]
    exact ⟨Finset.univ.image z, by simp [F₀]⟩
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F₀
  have htr : Algebra.trdeg k F₀ = Algebra.trdeg k (Algebra.adjoin k (Set.range z)) := by
    have := trdeg_add_eq k (Algebra.adjoin k (Set.range z)) (A := F₀)
    rw [trdeg_eq_zero (R := Algebra.adjoin k (Set.range z)) (A := F₀), add_zero] at this
    exact this.symm
  have hcard : s.card ≤ e := by
    have h1 := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, htr] at h1
    exact_mod_cast h1 ▸ he
  let N : Submodule F₀ Ω[F₀⁄k] :=
    Submodule.span F₀ (Set.range fun x : s => KaehlerDifferential.D k F₀ x)
  have hspan : N = ⊤ := by
    have hD := DerivSpanTrdeg.derivation_eq_zero_of_isSeparable (M := Ω[F₀⁄k] ⧸ N) (s : Set F₀)
      (N.mkQ.compDer (KaehlerDifferential.D k F₀)) (fun x hx => by
        change N.mkQ (KaehlerDifferential.D k F₀ x) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have := congrArg (fun D => D x) hD
    simpa [Submodule.Quotient.mk_eq_zero] using this
  have hr : Module.finrank F₀ Ω[F₀⁄k] ≤ e := by
    have h := finrank_range_le_card (R := F₀) (fun x : s => KaehlerDifferential.D k F₀ x)
    change Module.finrank F₀ N ≤ _ at h
    rw [hspan, finrank_top, Fintype.card_coe] at h
    exact h.trans hcard
  let ω := Module.finBasis F₀ Ω[F₀⁄k]
  refine ⟨Module.finrank F₀ Ω[F₀⁄k], hr, fun m j =>
    ω.repr (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) m, ?_⟩
  intro D
  let D' : Derivation k F₀ L := D.compAlgebraMap F₀
  let φ := (KaehlerDifferential.linearMapEquivDerivation k F₀).symm D'
  refine ⟨fun m => φ (ω m), fun j => ?_⟩
  have h1 : D (z j) =
      φ (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) := by
    have h := LinearEquiv.apply_symm_apply (KaehlerDifferential.linearMapEquivDerivation k F₀) D'
    exact (congrArg (fun D'' : Derivation k F₀ L =>
      D'' ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) h).symm

  rw [h1, ← ω.sum_repr (KaehlerDifferential.D k F₀ _), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def, mul_comm]
  rfl

end

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenericFormsKer

section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem GenericFormsKer.proof : GenericFormsKer.Statement := by
  intro F L _ _ _ ι _ e r hre u hu b c h j
  classical

  set V : Submodule F (ι → F) := Submodule.span F (Set.range b) with hV
  set B := Module.finBasis F V
  set r' := Module.finrank F V
  have hr' : r' ≤ e := (finrank_range_le_card b).trans (by simpa using hre)
  let v : Fin r' → ι → F := fun l => (B l : ι → F)
  have hbm : ∀ m, b m ∈ V := fun m => Submodule.subset_span ⟨m, rfl⟩

  let c' : Fin r' → L := fun l => ∑ m, c m * algebraMap F L (B.repr ⟨b m, hbm m⟩ l)
  have hw : ∀ j, ∑ m, c m * algebraMap F L (b m j) = ∑ l, c' l * algebraMap F L (v l j) := by
    intro j
    have hexp : ∀ m, b m j = ∑ l, B.repr ⟨b m, hbm m⟩ l * v l j := by
      intro m
      have := congrFun (congrArg Subtype.val (B.sum_repr ⟨b m, hbm m⟩)) j
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      exact this.symm

    simp only [hexp, map_sum, map_mul, Finset.mul_sum, c', Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring

  let M : Matrix (Fin r') (Fin r') L :=
    fun i l => ∑ j, u (Fin.castLE hr' i, j) * algebraMap F L (v l j)
  have hMc : M.mulVec c' = 0 := by
    funext i
    have hi := h (Fin.castLE hr' i)
    simp only [hw] at hi
    simp only [Matrix.mulVec, dotProduct, M, Pi.zero_apply, Finset.sum_mul]
    rw [Finset.sum_comm, ← hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

  let P : Matrix (Fin r') (Fin r') (MvPolynomial (Fin e × ι) F) :=
    fun i l => ∑ j, X (Fin.castLE hr' i, j) * C (v l j)
  have hPM : (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L).toRingHom.mapMatrix P = M := by
    ext i l
    change aeval u (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = M i l

    simp only [map_sum, map_mul, aeval_X, aeval_C, M]

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  let A₀ : Fin r' → ι → F := fun l j => B.repr (g (Pi.single j 1)) l
  have hA₀ : ∀ i l, ∑ j, A₀ i j * v l j = if i = l then 1 else 0 := by
    intro i l
    have hvl : (∑ j, v l j • (Pi.single j (1 : F) : ι → F)) = V.subtype (B l) := by
      funext k
      simp [v, Finset.sum_apply, Pi.single_apply]
    have := congrArg (fun x => B.repr (g x) i) hvl

    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul] at this
    rw [← LinearMap.comp_apply, hg, LinearMap.id_apply, Module.Basis.repr_self_apply] at this
    have hil : (if i = l then (1 : F) else 0) = if l = i then 1 else 0 := by
      by_cases hh : i = l
      · simp [hh]
      · simp [hh, Ne.symm hh]
    rw [hil, ← this]
    simp only [A₀]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  let x : Fin e × ι → F := fun p => if hp : p.1.val < r' then A₀ ⟨p.1.val, hp⟩ p.2 else 0
  have hPx : (eval x).mapMatrix P = 1 := by
    ext i l
    change eval x (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = (1 : Matrix (Fin r') (Fin r') F) i l

    simp only [map_sum, map_mul, eval_X, eval_C, Matrix.one_apply]
    rw [← hA₀]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [x, Fin.castLE]
  have hPdet : P.det ≠ 0 := by
    intro h0
    have := congrArg (eval x) h0
    rw [RingHom.map_det, hPx, Matrix.det_one, map_zero] at this
    exact one_ne_zero this
  have hMdet : M.det ≠ 0 := by
    rw [← hPM, ← RingHom.map_det]
    have hinj : Function.Injective (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L) :=
      algebraicIndependent_iff_injective_aeval.1 hu
    exact (map_ne_zero_iff _ hinj).2 hPdet
  have hc' : c' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hMdet hMc
  rw [hw]
  simp [hc']

end

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfFreeParAlgIndep

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

private theorem coneDim₃ : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem ChartPointTrdeg.full : ChartPointTrdeg.Statement :=
  ChartPointTrdeg.proof coneDim₃ GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
theorem SpecChart.full : SpecChart.Statement := SpecChart.proof
theorem GenericFormsKer.full : GenericFormsKer.Statement := GenericFormsKer.proof
theorem DerivSpanTrdeg.full : DerivSpanTrdeg.Statement := DerivSpanTrdeg.proof

theorem SecPointSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    SecPointSeparable.Statement :=
  SecPointSeparable.proof GenericFormsKer.full DerivSpanTrdeg.full h

theorem GenSecSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    GenSecSeparable.Statement :=
  GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h)

theorem ChowFormSectionVertical.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_chartPoint_secPoint_specChart ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h) SpecChart.full

end GroundTheory.Heights₂.Heights.Vertical
end
end
