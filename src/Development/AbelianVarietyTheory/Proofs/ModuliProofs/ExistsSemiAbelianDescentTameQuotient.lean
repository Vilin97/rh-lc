module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecOnNonvanishingOfTameQuotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotient
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenLeOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientOfFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullbackFlatOfTameStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientExistsUniqueCompEq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfIsPullbackOfSurjectiveOfFlat
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientDescendGrpObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ResidueFieldMapFiniteSeparableOfTame

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfInvGenOfInvariants

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LinDescent

variable {X Y Z : Scheme.{0}}

theorem sum_coeff_eq_zero_of_linearIndependent {R M ι C : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Fintype C] [DecidableEq ι] {v : ι → M} (hv : LinearIndependent R v) (p : C → ι)
    (a : C → R) (h : ∑ c, a c • v (p c) = 0) (i : ι) : ∑ c, (if p c = i then a c else 0) = 0 := by
  have h1 := linearIndependent_iff.1 hv (∑ c, Finsupp.single (p c) (a c)) (by
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, Finsupp.linearCombination_single] using h)
  have h2 := DFunLike.congr_fun h1 i
  simpa only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finsupp.zero_apply] using h2

variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}

theorem exists_inv_sec_of_tame [Group C] [Finite C] (hL : L.IsLB)
    (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      (Nat.card {c // r ≫ t c = r} : k) ≠ 0)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X) c, r ≫ t c = r →
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u c) r) (LB.oneGen L))
    {W : X.Opens} (hWa : IsAffineOpen W) (hW : ∀ c, W ≤ t c ⁻¹ᵁ W) (x : X) (hx : x ∈ W) :
    ∃ s : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W s ∧ IsInv u W s ∧
      ∃ i, x ∈ X.basicOpen (s i) := by
  classical
  cases nonempty_fintype C
  obtain ⟨m, hm, hm'⟩ := exists_locSec hL hWa x hx
  obtain ⟨k, _, _, r, hr⟩ := FinEt.exists_algClosed_point X x
  let z : Sp k := IsLocalRing.closedPoint k
  obtain rfl : r z = x := hr.le ⟨z, rfl⟩
  let ek := (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hF : IsField ((Sp k).presheaf.stalk z) := ek.toMulEquiv.isField (Field.toIsField k)
  have hz : ∀ c, (r ≫ t c) z ∈ W := fun c => hW c hx
  let p : C → (Γ(X, W) →* (Sp k).presheaf.stalk z) :=
    fun c => (gsHom (r ≫ t c) z W (hz c)).toMonoidHom
  have hp : ∀ c, p c = (gsHom r z W hx).toMonoidHom ↔ r ≫ t c = r := fun c =>
    ⟨fun e => hom_ext_of_gs hWa
      (fun z' => Subsingleton.elim z z' ▸ hz c) (fun z' => Subsingleton.elim z z' ▸ hx)
      fun z' f => by
        obtain rfl : z = z' := Subsingleton.elim _ _
        rw [gs_eq_gsHom _ _ _ (hz c), gs_eq_gsHom _ _ _ hx]
        exact DFunLike.congr_fun e f,
    fun e => MonoidHom.ext fun f => by
      change gsHom (r ≫ t c) z W (hz c) f = gsHom r z W hx f
      rw [← gs_eq_gsHom, ← gs_eq_gsHom, e]⟩
  choose J hJ using fun χ : Sp k ⟶ X => exists_chart hL (χ z)
  have hJ' : Good L z J := hJ
  have h1 : ∀ c, r ≫ t c = r → uv (u c) r z (J r) (J (r ≫ t c)) = 1 := fun c e => by
    have := val_corr hJ' (hfix k r c e) (𝟙 _)
    rwa [val_pull hJ', val_one, Category.id_comp, val_eq_uv] at this
  have : ∃ f : Γ(X, W), ∑ c, (uv (u c) r z (J r) (J (r ≫ t c))).val *
      gs (r ≫ t c) z _ (m (J (r ≫ t c))) * gs (r ≫ t c) z W f ≠ 0 := by
    by_contra! H
    have h2 := sum_coeff_eq_zero_of_linearIndependent
      (linearIndependent_monoidHom Γ(X, W) ((Sp k).presheaf.stalk z)) p
      (fun c => (uv (u c) r z (J r) (J (r ≫ t c))).val * gs (r ≫ t c) z _ (m (J (r ≫ t c))))
      (funext fun f => by
        rw [Finset.sum_apply]
        refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (H f)
        rw [gs_eq_gsHom _ _ _ (hz c) f]
        rfl) (gsHom r z W hx).toMonoidHom
    have h3 : ∀ c, (if p c = (gsHom r z W hx).toMonoidHom then
        (uv (u c) r z (J r) (J (r ≫ t c))).val * gs (r ≫ t c) z _ (m (J (r ≫ t c))) else 0) =
        if r ≫ t c = r then gs r z _ (m (J r)) else 0 := fun c =>
      if_ctx_congr (hp c) (fun e => by rw [h1 c e, Units.val_one, one_mul, e]) fun _ => rfl
    rw [Finset.sum_congr rfl fun c _ => h3 c, ← Finset.sum_filter, Finset.sum_const,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, nsmul_eq_mul] at h2
    have h4 : IsUnit (gs r z _ (m (J r))) :=
      (isUnit_gs_iff r z (W ⊓ L.U (J r)) ⟨hx, hJ r⟩ _).2 (hm' _ (hJ r))
    have h5 := congrArg ek (h4.mul_left_eq_zero.1 h2)
    rw [map_natCast, map_zero] at h5
    exact htame k r h5
  obtain ⟨f, hf⟩ := this
  obtain ⟨s, h1, h2, h3⟩ := exists_average hL ht hu hc hW hm f
  refine ⟨s, h1, h2, J r, (isUnit_gs_iff r z (W ⊓ L.U (J r)) ⟨hx, hJ r⟩ _).1 ?_⟩
  rw [h3 _ r z (J r) (fun c => J (r ≫ t c)) hx (hJ r) fun c => hJ _]
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel hf
  exact IsUnit.of_mul_eq_one _ hb

def FunctionsAreInvariants (t : C → (X ⟶ X)) (π : X ⟶ Y) : Prop :=
  ∀ V : Y.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
    (∀ c (h : π ⁻¹ᵁ V ≤ t c ⁻¹ᵁ (π ⁻¹ᵁ V)), ((t c).appLE _ _ h).hom f = f) →
      f ∈ Set.range (π.app V).hom

theorem FunctionsAreInvariants.exists_descend (h : FunctionsAreInvariants t π) (V : Y.Opens)
    (f : Γ(X, π ⁻¹ᵁ V))
    (hf : ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ t c) z _ f = gs r z _ f) :
    ∃ a : Γ(Y, V), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ π) z V a = gs r z _ f := by
  obtain ⟨a, rfl⟩ := (h V).2 f fun c e => fn_ext fun x hx =>
    (gs_appLE (𝟙 X) (t c) x _ _ e hx f).trans (hf c X (𝟙 X) x hx)
  exact ⟨a, fun Z r z hz => (gs_pull r π z V hz a).symm⟩

theorem FunctionsAreInvariants.unit_ext (h : FunctionsAreInvariants t π) {V : Y.Opens}
    {a b : Γ(Y, V)ˣ} (e : ∀ x, π x ∈ V → gm (𝟙 X ≫ π) x V a = gm (𝟙 X ≫ π) x V b) : a = b := by
  refine Units.ext ((h V).1 (fn_ext fun x hx => ?_))
  rw [gs_pull (𝟙 X) π x V hx, gs_pull (𝟙 X) π x V hx, gs_unit (𝟙 X ≫ π) x V hx,
    gs_unit (𝟙 X ≫ π) x V hx, e x hx]

theorem exists_descent_of_invGen_of_invariants [Surjective π] (hL : L.IsLB)
    (hπ : ∀ c, t c ≫ π = π) (h : FunctionsAreInvariants t π) {u : ∀ c, LB.Gen (twist L (t c))}
    (V : Y → Y.Opens) (hV : ∀ y, y ∈ V y) (e : ∀ y i, Γ(X, π ⁻¹ᵁ V y ⊓ L.U i)ˣ)
    (he : ∀ y, IsInvGen u (π ⁻¹ᵁ V y) (e y)) :
    ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  have hmem : ∀ (U : Y.Opens) c {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ U →
      (r ≫ t c) z ∈ π ⁻¹ᵁ U := fun U c Z r z hz => by
    change ((r ≫ t c) ≫ π) z ∈ U
    rw [Category.assoc, hπ]
    exact hz
  have H : ∀ y y', ∃ g : Γ(Y, V y ⊓ V y')ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i,
      r z ∈ π ⁻¹ᵁ V y → r z ∈ π ⁻¹ᵁ V y' → r z ∈ L.U i →
      gm (r ≫ π) z _ g = gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹ := fun y y' => by
    let O : L.ι → X.Opens := fun i => π ⁻¹ᵁ (V y ⊓ V y') ⊓ L.U i
    have l : ∀ i, O i ≤ π ⁻¹ᵁ V y ⊓ L.U i := fun i x hx => ⟨hx.1.1, hx.2⟩
    have l' : ∀ i, O i ≤ π ⁻¹ᵁ V y' ⊓ L.U i := fun i x hx => ⟨hx.1.2, hx.2⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ O i →
        gs r z (O i) (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val =
        (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val := fun Z r z i hz => by
      rw [gs_unit r z _ hz, map_mul, map_inv, gm_res r z _ hz, gm_res r z _ hz]
    obtain ⟨ρ, hρ⟩ := glue_fn (π ⁻¹ᵁ (V y ⊓ V y')) O (fun _ => inf_le_left)
      (fun x hx => (exists_chart hL x).imp fun i hi => ⟨hx, hi⟩)
      (fun i => (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val) (fun i j x hi hj => by
        rw [v _ (𝟙 X) x i hi, v _ (𝟙 X) x j hj, (he y).1 _ (𝟙 X) x i j hi.1.1 hi.2 hj.2,
          (he y').1 _ (𝟙 X) x i j hi.1.2 hi.2 hj.2, ← div_eq_mul_inv, mul_div_mul_left_eq_div,
          div_eq_mul_inv])
    have hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ (V y ⊓ V y') →
        r z ∈ L.U i → gs r z _ ρ = (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val :=
      fun Z r z i h1 h2 => (hρ Z r z i ⟨h1, h2⟩).trans (v Z r z i ⟨h1, h2⟩)
    obtain ⟨a, ha⟩ := h.exists_descend (V y ⊓ V y') ρ fun c Z r z hz => by
      obtain ⟨i, hi⟩ := exists_chart hL (r z)
      obtain ⟨k, hk⟩ := exists_chart hL ((r ≫ t c) z)
      rw [hρ' Z r z i hz hi, hρ' Z (r ≫ t c) z k (hmem _ c r z hz) hk,
        (he y).2 c Z r z i k hz.1 hi hk, (he y').2 c Z r z i k hz.2 hi hk,
        ← div_eq_mul_inv (_ * _), mul_div_mul_left_eq_div, div_eq_mul_inv]
    have hu : IsUnit a := isUnit_of_mem_basicOpen a fun b hb => by
      obtain ⟨x, rfl⟩ := π.surjective b
      obtain ⟨i, hi⟩ := exists_chart hL x
      refine (isUnit_gs_iff (𝟙 X ≫ π) x (V y ⊓ V y') hb a).1 ?_
      rw [ha _ (𝟙 X) x hb, hρ' _ (𝟙 X) x i hb hi]
      exact Units.isUnit _
    refine ⟨hu.unit, fun Z r z i h1 h2 hi => Units.ext ?_⟩
    exact (gs_unit (r ≫ π) z (V y ⊓ V y') ⟨h1, h2⟩ hu.unit).symm.trans
      ((ha Z r z ⟨h1, h2⟩).trans (hρ' Z r z i ⟨h1, h2⟩ hi))
  choose g hg using H
  let M : LB Y := ⟨Y, V, g⟩
  refine ⟨M, ⟨eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hV y⟩, fun y => ?_,
    fun y₁ y₂ y₃ => ?_⟩, ?_⟩
  · refine h.unit_ext fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine (gm_res (𝟙 X ≫ π) x _ hx _).trans ((hg y y _ (𝟙 X) x i hx hx hi).trans ?_)
    rw [mul_inv_cancel, map_one]
  · refine h.unit_ext fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₁ y₂ _ (𝟙 X) x i hx.1.1 hx.1.2 hi))
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₂ y₃ _ (𝟙 X) x i hx.1.2 hx.2 hi)))).trans
      (Eq.trans ?_ ((gm_res (𝟙 X ≫ π) x _ hx _).trans
        (hg y₁ y₃ _ (𝟙 X) x i hx.1.1 hx.2 hi)).symm)
    rw [mul_comm, mul_assoc, inv_mul_cancel_left]
  · have l : ∀ p : (PUnit → Y) × L.ι, (M.pull π).U p.1 ⊓ L.U p.2 ≤
        π ⁻¹ᵁ V (p.1 PUnit.unit) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.1 hx.1, hx.2⟩
    let w : LB.Iso L (M.pull π) := ⟨fun p => (res (l p) (e (p.1 PUnit.unit) p.2))⁻¹⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (y : Y) i, π (r z) ∈ V y → r z ∈ L.U i →
        gw w r z y i = (gm r z _ (e y i))⁻¹ := fun Z r z y i h1 h2 =>
      (map_inv _ _).trans (congrArg _ (gm_res r z (l (fun _ => y, i))
        ⟨(mem_pull (L := M)).2 h1, h2⟩ _))
    refine ⟨w, (isGen_iff w).2 fun Z r z y y' i i' h1 h2 h3 h4 => ?_⟩
    rw [v Z r z y i h1 h3, v Z r z y' i' h2 h4]
    refine Eq.trans ?_ (congrArg (· * _ * _) (hg y y' Z r z i' h1 h2 h4)).symm
    rw [(he y).1 Z r z i i' h1 h3 h4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem exists_descent_of_tame_family [Group C] [Finite C] [IsIntegralHom π] [Surjective π]
    (hL : L.IsLB) (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (hπ : ∀ c, t c ≫ π = π) (h : FunctionsAreInvariants t π)
    (horb : ∀ x x' : X, π x = π x' → ∃ c, x = t c x')
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      (Nat.card {c // r ≫ t c = r} : k) ≠ 0)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X) c, r ≫ t c = r →
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u c) r) (LB.oneGen L)) :
    ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e, IsInvGen u (π ⁻¹ᵁ V) e := fun y => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (π x)) isOpen_univ
    have hinv : ∀ (V : Y.Opens) c, π ⁻¹ᵁ V ≤ t c ⁻¹ᵁ π ⁻¹ᵁ V := fun V c => by
      rw [← Scheme.Hom.comp_preimage, hπ]
    obtain ⟨s, h1, h2, i₀, h3⟩ := exists_inv_sec_of_tame hL ht htame hu hc hfix
      (IsAffineOpen.preimage hV₀ π) (hinv V₀) x hx
    let N : X.Opens := ⨆ i, X.basicOpen (s i)
    let V : Y.Opens := ⟨(π '' (N : Set X)ᶜ)ᶜ, (π.isClosedMap _ N.isOpen.isClosed_compl).isOpen_compl⟩
    have hN : ∀ x', x' ∈ π ⁻¹ᵁ V → ∃ i, x' ∈ X.basicOpen (s i) := fun x' hx' => by
      by_contra hh
      exact hx' ⟨x', fun hh' => hh (Opens.mem_iSup.1 hh'), rfl⟩
    have hN' : ∀ x', x' ∈ π ⁻¹ᵁ V → x' ∈ π ⁻¹ᵁ V₀ := fun x' hx' => by
      obtain ⟨i, hi⟩ := hN x' hx'
      exact (X.basicOpen_le _ hi).1
    have l : ∀ i, π ⁻¹ᵁ V ⊓ L.U i ≤ π ⁻¹ᵁ V₀ ⊓ L.U i := fun i x' hx' => ⟨hN' x' hx'.1, hx'.2⟩
    have hu' : ∀ i, IsUnit (rs (l i) (s i)) := fun i => isUnit_of_mem_basicOpen _ fun x' hx' => by
      obtain ⟨j, hj⟩ := hN x' hx'.1
      have hj' := X.basicOpen_le _ hj
      refine (isUnit_gs_iff (𝟙 X) x' _ hx' _).1 ?_
      rw [gs_res (𝟙 X) x' _ hx', h1 _ (𝟙 X) x' i j hj'.1 hx'.2 hj'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X) x' _ hj' _).2 hj)
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ V → r z ∈ L.U i →
        (gm r z _ (hu' i).unit).val = gs r z _ (s i) := fun Z r z i a b =>
      (gs_unit r z (π ⁻¹ᵁ V ⊓ L.U i) ⟨a, b⟩ _).symm.trans (gs_res r z (l i) ⟨a, b⟩ _)
    refine ⟨V, ?_, fun i => (hu' i).unit, fun Z r z i j a b c => Units.ext ?_,
      fun c Z r z i k a b d => Units.ext ?_⟩
    · rintro ⟨x', hx', e⟩
      obtain ⟨c, rfl⟩ := horb _ _ e
      obtain ⟨k, hk⟩ := exists_chart hL (t c x)
      have h4 := X.basicOpen_le _ h3
      have h5 := (isUnit_gs_iff (𝟙 X) x _ h4 _).2 h3
      rw [h2 c _ (𝟙 X) x i₀ k hx h4.2 hk] at h5
      exact hx' (Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff (𝟙 X ≫ t c) x (π ⁻¹ᵁ V₀ ⊓ L.U k)
        ⟨hinv V₀ c hx, hk⟩ _).1 (isUnit_of_mul_isUnit_right h5)⟩)
    · rw [Units.val_mul, v Z r z i a b, v Z r z j a c]
      exact h1 Z r z i j (hN' _ a) b c
    · rw [Units.val_mul, v Z r z i a b, v Z (r ≫ t c) z k (hinv V c a) d]
      exact h2 c Z r z i k (hN' _ a) b d
  choose V hV e he using H
  exact exists_descent_of_invGen_of_invariants hL hπ h V hV e he

end GlobalTheory.LinDescent

namespace GlobalTheory.LinDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

theorem exists_descent_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y Y' : Scheme.{0}) (τ : Γ →* Aut Y) (φ : Y ⟶ Y') (L : LB Y), (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), (Nat.card {g // x ≫ (τ g).asIso.hom = x} : k) ≠ 0) → L.IsLB → ∀ u : ∀ g, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, (τ g).asIso.hom] ![1, -1]), (∀ g, (u g).IsGen) → (∀ g h, LB.Gen.Corr L _ _ _ _ (u (h * g)) (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).asIso.hom))) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) g, y ≫ (τ g).asIso.hom = y → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u g) y) (LB.oneGen L)) → ∃ L' : LB Y', L'.IsLB ∧ LBIso L (L'.pull φ) := by
  intro Γ _ _ Y Y' τ φ L hφ htame hL u hu hc hfix
  obtain ⟨_, _, horb, -, -⟩ := quotient_isIntegral_surjective_orbits Γ Y Y' τ φ hφ
  have : Finite Γᵐᵒᵖ := Finite.of_equiv Γ MulOpposite.opEquiv
  refine exists_descent_of_tame_family (C := Γᵐᵒᵖ) (t := fun c => (τ c.unop).asIso.hom) hL
    (fun c c' => ?_) (fun c => hφ.2.1 _)
    (fun V => ⟨(hφ.2.2 V).1, fun f hf => (hφ.2.2 V).2 f fun g => hf (MulOpposite.op g)⟩)
    (fun x x' e => ?_) (fun k _ _ r => ?_) (u := fun c => u c.unop) (fun c => hu _)
    (fun c c' => hc c.unop c'.unop) (fun k _ _ r c => hfix k r c.unop)
  · beta_reduce
    rw [MulOpposite.unop_mul, map_mul]
    rfl
  · obtain ⟨g, hg⟩ := horb x' x e.symm
    exact ⟨MulOpposite.op g, hg⟩
  · rw [← Nat.card_congr (MulOpposite.opEquiv.subtypeEquiv
      (p := fun g : Γ => r ≫ (τ g).asIso.hom = r) fun g => Iff.rfl)]
    exact htame k r

end GlobalTheory.LinDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotientStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_semiAbelianTriple_of_finiteQuotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (a' : OAct (𝓞 E) G') (φ : t.G.left ⟶ G'.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → IsSemiAbelian G' → IsGrpPullback t.G G' π φ → (∀ x, (t.act.act x).left ≫ φ = φ ≫ (a'.act x).left) → L'.IsLB → LBIso t.PP.L (L'.pull φ) → ∃ (t' : SAB H X') (ν : SABMap t t' π) (e : t'.G ≅ G'), ν.φ ≫ e.hom.left = φ := by
  first | exact @GlobalTheory.QuotTriple.exists_sab_of_quotient | exact GlobalTheory.QuotTriple.exists_sab_of_quotient | (intros; apply GlobalTheory.QuotTriple.exists_sab_of_quotient <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothDescentOfTameQuotient

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem exists_smooth_descent_of_tame_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) (s : X ⟶ Sp R) (τ : Γ →* Aut G.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (G.hom ≫ s) → Smooth G.hom → (∀ g, (τ g).asIso.hom ≫ G.hom = G.hom ≫ (ρ g).asIso.hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst G.hom x ≫ (τ g).asIso.hom = pullback.fst G.hom x) → ∃ (G' : Over X') (φ : G.left ⟶ G'.left), IsPullback φ G.hom G'.hom π ∧ Smooth G'.hom ∧ ∀ g, (τ g).asIso.hom ≫ φ = φ := by
  intro Γ _ _ R _ X X' _ ρ π G s τ hπ hfin hqp hsm hτ hstab hfib
  have hsepG : G.left.IsSeparated := by
    obtain ⟨N, i, hi, -, hcomp⟩ := hqp
    haveI := isProper_str R N
    haveI : IsSeparated (G.hom ≫ s) := by rw [← hcomp]; infer_instance
    constructor
    rw [show terminal.from G.left = (G.hom ≫ s) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨Y', φ, hφ⟩ := exists_quotient_of_finite_group Γ G.left τ (fun y => by
    obtain ⟨V, hV, hF, -⟩ := exists_isAffineOpen_le_of_isQProjOver R G.left (G.hom ≫ s) hqp
      (Set.range fun g => (τ g).asIso.hom y) ⊤ (Set.finite_range _) (fun _ _ => trivial)
    exact ⟨V, hV, fun g => hF ⟨g, rfl⟩⟩)
  obtain ⟨p', hp', -⟩ := quotient_existsUnique_comp_eq Γ G.left Y' τ φ hφ X' (G.hom ≫ π)
    (fun g => by rw [← Category.assoc, hτ g, Category.assoc, hπ.2.1 g])
  obtain ⟨hpb, hflat, hlft⟩ := GlobalTheory.T.isPullback_flat_of_tame_alt Γ X X' G.left Y' ρ τ π φ G.hom p' hπ hφ hp' hτ hfin
    inferInstance inferInstance hstab hfib
  have hsurj : Surjective π := (quotient_isIntegral_surjective_orbits Γ X X' ρ π hπ).2.1
  haveI : LocallyOfFinitePresentation p' := inferInstance
  exact ⟨Over.mk p', φ, hpb,
    smooth_of_isPullback_of_surjective_of_flat X X' G.left Y' π φ G.hom p' hpb hsurj hflat
      inferInstance hsm, fun g => hφ.2.1 g⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianDescentTameQuotient

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem fixes_iff_fixes_image {X Y T : Scheme.{0}} (p : Y ⟶ X) (r : X ⟶ X) (q : Y ⟶ Y) (y : T ⟶ Y)
    (w : q ≫ p = p ≫ r)
    (h : (y ≫ p) ≫ r = y ≫ p → pullback.fst p (y ≫ p) ≫ q = pullback.fst p (y ≫ p)) :
    y ≫ q = y ↔ (y ≫ p) ≫ r = y ≫ p := by
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [Category.assoc, ← w, ← Category.assoc, hy]
  · have := pullback.lift y (𝟙 _) (Category.id_comp _).symm ≫= h hy
    rwa [pullback.lift_fst_assoc, pullback.lift_fst] at this

theorem exists_sab_descent_of_tame_quotient :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (s : X ⟶ Sp R) (τ : Γ →* Aut t.G.left) (mu : ∀ g, SABMap t t (ρ g).asIso.hom), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (t.G.hom ≫ s) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → (∀ g, (mu g).φ = (τ g).asIso.hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst t.G.hom x ≫ (τ g).asIso.hom = pullback.fst t.G.hom x) → ∃ (t' : SAB H X') (ν : SABMap t t' π), (∀ g, (τ g).asIso.hom ≫ ν.φ = ν.φ) ∧ (Good t → PushInvertible t.G t.PP.L → Good t') := by
  intro E _ _ _ H Γ _ _ R _ X X' _ ρ π t s τ mu hQ hfin hqp hga hmu htame hfib
  have hsemi := t.semi
  have hcart (g : Γ) : IsGrpPullback t.G t.G (ρ g).asIso.hom (τ g).asIso.hom := hmu g ▸ (mu g).cart
  have hw (g : Γ) : (τ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ g).asIso.hom := (hcart g).1.w
  have hact (g : Γ) (c) : (t.act.act c).left ≫ (τ g).asIso.hom = (τ g).asIso.hom ≫ (t.act.act c).left :=
    hmu g ▸ (mu g).act c
  have he (g : Γ) : eSec t.G ≫ (τ g).asIso.hom = (ρ g).asIso.hom ≫ eSec t.G := by
    have := (mu g).cm.e_comm
    rw [(mu g).base] at this
    rw [← hmu g]
    exact this
  have hL (g : Γ) : LBIso t.PP.L (t.PP.L.pull (τ g).asIso.hom) := by
    obtain ⟨w, hw, -⟩ := (mu g).lin
    rw [← hmu g]
    exact ⟨w, hw⟩
  have hsec : eSec t.G ≫ t.G.hom = 𝟙 X := Over.w (η[t.G])
  have hgi : GeometricallyIntegral t.G.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hsemi.smooth hsemi.geomConnected
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hQ
  obtain ⟨G', φ, hpb, hsm, hinv⟩ :=
    exists_smooth_descent_of_tame_quotient Γ R X X' ρ π t.G s τ hQ hfin hqp hsemi.smooth hw htame hfib
  obtain ⟨_, _, a', hgp, ha⟩ := quotient_descend_grpObj Γ (𝓞 E) X X' ρ π t.G G' φ τ t.act hQ hpb inferInstance
    fun g => ⟨hinv g, hcart g, hact g⟩
  have hsemi' := (SemiAbelianDescent.main X X' π t.G G' φ inferInstance hsurj hgp hsm hsemi).1
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := RigidLinearisation.exists_linearisation Γ X t.G (eSec t.G) ρ τ t.PP.L hsec hgi
    (eq_one_of_appLE_section_eq_one X t.G (eSec t.G) hsec hsemi.smooth hgi hga) (fun g => ⟨hw g, he g⟩) hfib
    t.PP.isLB ⟨t.PP.rig, t.PP.rigGen⟩ hL
  have hQ' := (quotient_flat_baseChange Γ X X' _ _ ρ π φ t.G.hom G'.hom hQ hpb inferInstance).2 τ
    fun g => ⟨hinv g, hw g⟩
  obtain ⟨L', hL', hiso⟩ := LinDescent.exists_descent_of_tame Γ _ _ τ φ t.PP.L hQ' (fun k _ _ y => by
    convert htame k (y ≫ t.G.hom) using 2
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
      fixes_iff_fixes_image t.G.hom _ _ y (hw g) (hfib k _ g))) t.PP.isLB u hu₁ hu₂ hu₃
  obtain ⟨t', ν, e, hν⟩ := T.exists_semiAbelianTriple_of_finiteQuotient E H Γ X X' ρ π t G' a' φ L' hQ hga hsemi' hgp ha hL' hiso
  have hinv' (g : Γ) : (τ g).asIso.hom ≫ ν.φ = ν.φ := by
    rw [← cancel_mono e.hom.left, Category.assoc, hν, hinv]
  refine ⟨t', ν, hinv', fun ⟨h₁, h₂, _⟩ hP => ⟨?_, ?_, ?_⟩⟩
  · exact (SemiAbelianDescent.main X X' π t.G t'.G ν.φ inferInstance hsurj ν.cart t'.semi.smooth hsemi).2 h₁
  · exact splitFibres_descend_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ hQ htame ν.cart h₂
  · obtain ⟨w, hw', -⟩ := ν.lin
    have := t'.semi.smooth
    exact exists_secOn_nonvanishing_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ τ t.PP.L t'.PP.L hQ ν.cart.1
      inferInstance (fun g => ⟨hinv' g, hw g⟩) htame hfib t.PP.isLB t'.PP.isLB ⟨w, hw'⟩ hP

end GlobalTheory
end
end
