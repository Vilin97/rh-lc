module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValUnitNeZero
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallPowDvdGerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitAlgebraMapEqOfValuationEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.Basify
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsZpowMulIsUnitOfMem

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc TopologicalSpace

section Points
variable {K C : Type} [Field K] [Field C] [IsAlgClosed C] {Y : Scheme.{0}} {q : Y ⟶ Sp K} [LocallyOfFiniteType q]
  {σ : K →+* C}


variable (q σ) in
theorem exists_point_mem {Z : Set Y} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Sp C ⟶ Y, x ≫ q = spMap σ ∧ ∀ w, x w ∈ Z := by
  have hs : Surjective (spMap σ) := ⟨fun y ↦ by
    obtain ⟨z⟩ : Nonempty ↥(Sp C) := inferInstance
    exact ⟨z, Subsingleton.elim _ _⟩⟩
  have hJ : JacobsonSpace ↥(pullback q (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd q (spMap σ))
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z₀, rfl⟩ := (pullback.fst q (spMap σ)).surjective y
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints (Z := pullback.fst q (spMap σ) ⁻¹' Z) ⟨z₀, hy⟩
    (hZ.preimage (pullback.fst q (spMap σ)).continuous)
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (pullback.snd q (spMap σ)) z hz ≫ pullback.fst _ _,
    by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc], fun w => ?_⟩
  rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  exact hzZ

theorem eq_of_val_eq [IsReduced Y] {W : Y.Opens} {r s : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r = valR x W s) : r = s := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ (Y.basicOpen (r - s)).isOpen.isLocallyClosed ⟨y, hy⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => Y.basicOpen_le _ (hm w)
  have := ((isUnit_valR_iff x W hW (r - s)).2 fun w _ => hm w).ne_zero
  rw [valR_eq x W hW, map_sub, ← valR_eq, ← valR_eq, h x hx hW, sub_self] at this
  exact (this rfl).elim

theorem isUnit_of_val_ne_zero {W : Y.Opens} {r : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r ≠ 0) : IsUnit r := by
  refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => (Scheme.mem_basicOpen _ _ y hy).1 ?_
  by_contra hn
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ
    (W.isOpen.isLocallyClosed.inter (Y.basicOpen r).isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hn⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => (hm w).1
  obtain ⟨w⟩ : Nonempty ↥(Sp C) := inferInstance
  exact (hm w).2 ((isUnit_valR_iff x W hW r).1 (h x hx hW).isUnit (show w ∈ (⊤ : (Sp C).Opens) from trivial))

theorem exists_glue [IsReduced Y] {I : Type} (W : Y.Opens) (T : I → Y.Opens) (F : I → (Sp C ⟶ Y) → C)
    (hT : ∀ z, ∃ m, z ∈ T m) (hF : ∀ m, Reg q σ (W ⊓ T m) (F m))
    (h : ∀ m m' x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F m x = F m' x) :
    ∃ r : Γ(Y, W), ∀ m x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → F m x = valR x W r := by
  choose u hu using hF
  obtain ⟨r, hr, -⟩ := Y.sheaf.existsUnique_gluing' (fun m => W ⊓ T m) W (fun _ => homOfLE inf_le_left)
    (fun y hy => Opens.mem_iSup.2 ((hT y).imp fun _ hm => ⟨hy, hm⟩)) u
    (fun m m' => eq_of_val_eq (q := q) (σ := σ) (W := W ⊓ T m ⊓ (W ⊓ T m')) fun x hx hW =>
      (valR_res x inf_le_left hW _).trans ((hu m x hx fun _ hz => (hW hz).1).symm.trans
        ((h m m' x hx (fun _ hz => (hW hz).1.1) (fun _ hz => (hW hz).1.2) fun _ hz => (hW hz).2.2).trans
          ((hu m' x hx fun _ hz => (hW hz).2).trans (valR_res x inf_le_right hW _).symm))))
  refine ⟨r, fun m x hx hW hm => ?_⟩
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ T m) := fun _ hz => ⟨hW hz, hm hz⟩
  rw [hu m x hx hh, ← hr m]
  exact valR_res x inf_le_left hh r

end Points


open GlobalTheory.PrimeSection in
theorem exists_zpow_mul_isUnit_of_mem {X : Scheme.{0}} {t : Γ(X, ⊤)} {ξ : X}
    (hη : ∀ x : X, x ∉ X.basicOpen t ↔ ξ ⤳ x)
    (hp : ∀ U : X.Opens, IsAffineOpen U → ξ ∈ U → Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
    [IsIntegral X] [IsLocallyNoetherian X] {A : Type} {U : A → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
    {a₀ : A} (h₀ : ξ ∈ U a₀) (hg : ∀ a b, IsUnit (g a b)) (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hru : ∀ a, IsUnit (r a)) :
    ∃ n : ℤ, ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
  obtain ⟨hdvr, hirr⟩ := isDiscreteValuationRing_stalk hη hp
  have hD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hx₀ : X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀) (r a₀) ≠ 0 := ((hru a₀).map _).ne_zero
  have hτn : ∀ n : ℤ, X.presheaf.germ _ _ hD (↑(τ ^ n) : Γ(X, X.basicOpen t)) =
      algebraMap _ X.functionField (X.presheaf.germ ⊤ ξ trivial t) ^ n := fun n ↦ by
    rw [algebraMap_germ, ← germ_res (le_top : X.basicOpen t ≤ ⊤) hD, ← hτ]
    let φ : Γ(X, X.basicOpen t) →+* X.functionField := (X.presheaf.germ _ _ hD).hom
    change φ _ = φ _ ^ n
    rw [← MonoidHom.coe_coe, ← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨n, ⟨u, hu, hn⟩, -⟩ :=
    GlobalTheory.PrimeElement.existsUnique_zpow_mul_eq_unit (K := X.functionField) hirr hx₀
  have : ∀ a, ∃ s : Γ(X, U a), X.presheaf.map (homOfLE inf_le_left).op s =
      X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a :=
    fun a ↦ exists_res_eq hη hp _ fun h ↦
      ⟨X.presheaf.germ (U a ⊓ U a₀) ξ ⟨h, h₀⟩ (g a a₀) * u, by
        rw [map_mul, map_mul, hn, germ_res, hτn, algebraMap_germ,
          germ_eq_mul_germ hr (a := a) _ (genericPoint_mem_inf hp h₀)]
        ring⟩
  choose s hs using this
  have hs₀ : ξ ∈ X.basicOpen (s a₀) := by
    rw [X.mem_basicOpen _ ξ h₀]
    convert hu
    apply IsFractionRing.injective _ X.functionField
    have := congrArg (X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀)) (hs a₀)
    rw [map_mul, germ_res, germ_res, hτn] at this
    rw [algebraMap_germ, hn, this]
  refine ⟨n, s, fun b ↦ isUnit_of_isUnit_res hη hp ?_ fun h ↦
    mem_basicOpen_of_compatible hg (compatible_of_res_eq hD hr _ hs) h hs₀, hs⟩
  rw [hs b]
  exact ((Units.isUnit _).map _).mul (hru b)


open GlobalTheory.DvrModel GlobalTheory.PrimeSection in
theorem norm_const : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (A I : Type) (U : A → H.Opens) (T : I → HK.Opens) (F : A → I → (Sp (PadicAlgCl p) ⟶ HK) → PadicAlgCl p), (∀ z, ∃ m, z ∈ T m) → (∀ a m, Reg q σ (j ⁻¹ᵁ U a ⊓ T m) (F a m)) → (∀ a m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → F a m x ≠ 0) → (∀ a m m' x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F a m x = F a m' x) → (∀ a a', ∃ g : Γ(H, U a ⊓ U a')ˣ, ∀ m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a' → ⊤ ≤ x ⁻¹ᵁ T m → F a m x = valR (x ≫ j) (U a ⊓ U a') g.val * F a' m x) → ∃ κ : ℝ, 0 < κ ∧ ∀ a m (c : Sp (OO p) ⟶ H) x, c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ‖F a m x‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hsm hgi hK A I U T F hT hreg hne h₁ h₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hK
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isOpenImmersion_generic hK
  have := GlobalTheory.DvrModel.isIntegral hK
  have := GlobalTheory.DvrModel.isLocallyNoetherian f
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hK inferInstance
  have hη := notMem_basicOpen_iff_specializes hϖ hs
  by_cases hA : ∃ a₀, pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) (genericPoint _) ∈ U a₀
  swap
  · refine ⟨1, one_pos, fun a m c x hc _ _ ha _ => (hA ⟨a, mem_of_notMem_basicOpen hη
      (ha (show IsLocalRing.closedPoint (OO p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)) ?_⟩).elim⟩
    rw [notMem_basicOpen_iff f hϖ, ← Scheme.Hom.comp_apply, hc]
    exact IsLocalRing.comap_closedPoint jV
  obtain ⟨a₀, h₀⟩ := hA
  choose r hr using fun a => exists_glue (j ⁻¹ᵁ U a) T (F a) hT (hreg a) (h₁ a)
  choose g hg using h₂
  have hpt : ∀ x : Sp (PadicAlgCl p) ⟶ HK, ∃ m, ⊤ ≤ x ⁻¹ᵁ T m := fun x =>
    (hT _).imp fun m hm => (top_le_iff x _).2 hm
  have hru : ∀ a, IsUnit (r a) := fun a => isUnit_of_val_ne_zero (q := q) (σ := σ) fun x hx hW => by
    obtain ⟨m, hm⟩ := hpt x
    rw [← hr a m x hx hW hm]
    exact hne a m x hx hW hm
  have h0 : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hϖ.ne_zero
  let φ : K →+* Γ(HK, ⊤) := q.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨r', τ', hτ', hr', -, hu', E⟩ := exists_transport (opensRange_generic hϖ hK)
    (g := fun a b => (g a b).val) (fun a => rfl) r
    (fun a b => eq_of_val_eq (q := q) (σ := σ) fun x hx hW => by
      obtain ⟨m, hm⟩ := hpt x
      have ha : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := fun _ hz => (hW hz).1
      have hb : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U b := fun _ hz => (hW hz).2
      refine (valR_res x inf_le_left hW _).trans (((hr a m x hx ha hm).symm.trans (hg a b m x hx ha hb hm)).trans
        (Eq.symm ((valR_mul x _ hW _ _).trans (congrArg₂ (· * ·) (GlobalTheory.Points.valR_appLE x j _ hW _) ?_))))
      exact (valR_res x inf_le_right hW _).trans (hr b m x hx hb hm).symm)
    (Units.map φ.toMonoidHom (Units.mk0 _ h0)) (appTop_cst hK.w ϖ).symm
  obtain ⟨n, s, hsu, hs'⟩ := exists_zpow_mul_isUnit_of_mem hη (prime_res_generic hϖ hs) h₀
    (fun a b => (g a b).isUnit) τ' hτ' hr' fun a => hu' a (hru a)
  have hpos : 0 < ‖σ (algebraMap V K ϖ)‖ ^ n := zpow_pos (norm_pos_iff.2 ((map_ne_zero σ).2 h0)) n
  refine ⟨(‖σ (algebraMap V K ϖ)‖ ^ n)⁻¹, inv_pos.2 hpos, fun a m c x hc hx hq ha hm => ?_⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := by
    show ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a
    rw [hx]
    exact fun _ _ => ha trivial
  have e := congrArg (valR x _) ((E n a (s a)).1 (hs' a))
  have e₁ : valR x ⊤ (Units.map φ.toMonoidHom (Units.mk0 _ h0)).val = σ (algebraMap V K ϖ) :=
    (GlobalTheory.Points.valR_comp x q ⊤ _).symm.trans (by
      rw [hq]
      exact GlobalTheory.Points.valR_specMap (CommRingCat.ofHom σ) _)
  have e₂ : ((valR c (U a) (s a) : OO p) : PadicAlgCl p) = σ (algebraMap V K ϖ) ^ n * F a m x := by
    rw [hr a m x hq hW hm, ← e₁, ← val_zpow x (U := ⊤) (fun _ _ => trivial)]
    refine Eq.trans ?_ ((e.trans (valR_mul x _ hW _ _)).trans (congrArg (· * _) (valR_res x le_top hW _)))
    refine Eq.trans ?_ (GlobalTheory.Points.valR_appLE x j _ hW _).symm
    rw [hx]
    exact ((valR_spMap (OO p).subtype c _ ha).2 _).symm
  have e₃ : ‖((valR c (U a) (s a) : OO p) : PadicAlgCl p)‖ = 1 := by
    have hu : IsUnit (valR c (U a) (s a)) := by
      rw [valR_eq c _ ha]
      exact (hsu a).map _
    obtain ⟨d, hd⟩ := hu.exists_right_inv
    have e' := congrArg (fun z : OO p => ‖(z : PadicAlgCl p)‖) hd
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at e'
    exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _))
      (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  rw [e₂, norm_mul, norm_zpow] at e₃
  exact eq_inv_of_mul_eq_one_right e₃

end GlobalTheory.ZH.FrameNorm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormConstSec

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

theorem norm_const_gen : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (nH : H ⟶ H) (nK : HK ⟶ HK) (nX : X ⟶ X), nK ≫ j = j ≫ nH → nK ≫ ψ = ψ ≫ nX → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1])), α.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l l' : M.ι) (m : Fin 2 → L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (c ≫ nH) ⁻¹ᵁ M.U l' → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) → ⊤ ≤ (x ≫ ψ ≫ nX) ⁻¹ᵁ L.U (m 1) → ‖valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x l (m 0) ^ n ^ 2 * (ω (x ≫ nK) l' (m 1))⁻¹‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω nH nK nX hnj hnψ n α hα
  have ej : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ j = (x ≫ j) ≫ nH := fun x => by
    rw [Category.assoc, hnj, Category.assoc]
  have eψ : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ ψ = (x ≫ ψ) ≫ nX := fun x => by
    rw [Category.assoc, hnψ, Category.assoc]
  have w₀ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ L.U (m 0) := fun m => LB.wchart_le L ![𝟙 X, nX] m 0
  have w₁ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ nX ⁻¹ᵁ L.U (m 1) := fun m => LB.wchart_le L ![𝟙 X, nX] m 1
  have l₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {a : M.ι × M.ι}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) →
      ⊤ ≤ ((x ≫ nK) ≫ j) ⁻¹ᵁ M.U a.2 := fun h => by
    rw [ej]
    exact fun _ hz => (h hz).2
  have m₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {m}, ⊤ ≤ x ⁻¹ᵁ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m →
      ⊤ ≤ ((x ≫ nK) ≫ ψ) ⁻¹ᵁ L.U (m 1) := fun h => by
    rw [eψ]
    exact fun _ hz => w₁ _ (h hz)
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (M.ι × M.ι) (Fin 2 → L.ι)
    (fun a => M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) (fun m => ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m)
    (fun a m x => valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x a.1 (m 0) ^ n ^ 2 *
      (ω (x ≫ nK) a.2 (m 1))⁻¹)
    (fun z => exists_chart (LB.isLB_linComb hL ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1]) (ψ z))
    (fun a m => ((Reg.pull ψ inf_le_right _).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) ⊓ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m) a.1 (m 0)
        (fun _ hz => hz.1.1) fun _ hz => w₀ _ hz.2).1).pow _)).mul
      (hω.reg nK _ a.2 (m 1) (by rw [hnj]; exact fun _ hz => hz.1.2) (by rw [hnψ]; exact fun _ hz => w₁ _ hz.2)).2)
    (fun a m x _ ha hm => mul_ne_zero (mul_ne_zero (val_unit_ne_zero (x ≫ ψ) (U := LB.wchart L ![𝟙 X, nX] m) hm _)
      (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => (ha hz).1) fun _ hz => w₀ _ (hm hz))))
      (inv_ne_zero (hω.ne _ _ _ (l₁ ha) (m₁ hm))))
    (fun a m m' x _ ha hm hm' => by
      have hm₀ : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) := fun _ hz => w₀ _ (hm hz)
      have hm₀' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m' 0) := fun _ hz => w₀ _ (hm' hz)
      have e := (gen_val hα (x := x ≫ ψ) hm hm').trans (congrArg (· * _) (tv_linComb L _ _
        (fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m k (hm hz)) fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m' k (hm' hz)))
      rw [Fin.prod_univ_two] at e
      change valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val =
        tv L ((x ≫ ψ) ≫ 𝟙 X) (m 0) (m' 0) ^ ((n : ℤ) ^ 2) * tv L ((x ≫ ψ) ≫ nX) (m 1) (m' 1) ^ (-1 : ℤ) *
        valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m') (α.s m').val at e
      rw [Category.comp_id, ← eψ, zpow_neg_one,
        show ∀ z : PadicAlgCl p, z ^ ((n : ℤ) ^ 2) = z ^ n ^ 2 from fun z => by rw [← zpow_natCast, Nat.cast_pow]] at e
      beta_reduce
      rw [e, ← hω.right x a.1 (m 0) (m' 0) (fun _ hz => (ha hz).1) hm₀ hm₀',
        ← hω.right (x ≫ nK) a.2 (m 1) (m' 1) (l₁ ha) (m₁ hm) (m₁ hm'), mul_pow, mul_inv]
      ring)
    (fun a a' => by
      have e₁ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ M.U a.1 ⊓ M.U a'.1 :=
        inf_le_inf inf_le_left inf_le_left
      have e₂ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ nH ⁻¹ᵁ (M.U a.2 ⊓ M.U a'.2) :=
        fun _ hz => ⟨hz.1.2, hz.2.2⟩
      refine ⟨res e₁ (M.g a.1 a'.1) ^ ((n ^ 2 : ℕ) : ℤ) * res e₂ (pullU nH _ (M.g a.2 a'.2)) ^ (-1 : ℤ),
        fun m x _ ha ha' hm => ?_⟩
      have hh : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2)) :=
        fun _ hz => ⟨ha hz, ha' hz⟩
      have v₁ : valR (x ≫ j) _ (res e₁ (M.g a.1 a'.1)).val = tv M (x ≫ j) a.1 a'.1 := valR_res _ e₁ hh _
      have v₂ : valR (x ≫ j) _ (res e₂ (pullU nH _ (M.g a.2 a'.2))).val = tv M ((x ≫ nK) ≫ j) a.2 a'.2 := by
        rw [ej]
        exact val_res_pull _ nH e₂ hh _
      beta_reduce
      rw [Units.val_mul, valR_mul _ _ hh, val_zpow _ hh, val_zpow _ hh, v₁, v₂, zpow_natCast, zpow_neg_one,
        hω.left x a.1 a'.1 (m 0) (fun _ hz => (ha hz).1) (fun _ hz => (ha' hz).1) fun _ hz => w₀ _ (hm hz),
        hω.left (x ≫ nK) a.2 a'.2 (m 1) (l₁ ha) (l₁ ha') (m₁ hm), mul_pow, mul_inv]
      ring)
  refine ⟨κ, hκ, fun c x l l' m hc hx hq hl hl' hm hm' => h (l, l') m c x hc hx hq (fun _ hz => ⟨hl hz, hl' hz⟩)
    fun _ hz => Set.mem_iInter.2 fun k => ?_⟩
  fin_cases k
  · exact hm hz
  · exact hm' hz

theorem norm_const_sec : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (Y : Scheme.{0}) (π : Y ⟶ X) (ψ' : HK ⟶ Y), ψ' ≫ π = ψ → ∀ (N : ℕ) (J : Type) [Fintype J] (s : J → (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (N : ℤ))).Sec) (t : J → (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 H) (fun _ => (N : ℤ))).Sec) (b : Matrix J J K), (∀ (x : Sp (PadicAlgCl p) ⟶ HK) v, x ≫ q = spMap σ → Crd _ s (x ≫ ψ') v → Crd _ t (x ≫ j) ((b.map σ).mulVec v)) → (∀ (c : Sp (OO p) ⟶ H) w, c ≫ f = spMap jV → Crd _ t c w → ∃ i, IsUnit (w i)) → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l : M.ι) (m : L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → IsGreatest (Set.range fun i => ‖(b.map σ).mulVec (fun i => valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) (fun _ => m)) ((s i).f fun _ => m)) i * ω x l m ^ N‖) κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω Y π ψ' hψ N J _ s t b hlink hprim
  subst hψ
  let v : (Sp (PadicAlgCl p) ⟶ HK) → L.ι → J → PadicAlgCl p := fun x m i =>
    valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) fun _ => m) ((s i).f fun _ => m)
  let w : (Sp (PadicAlgCl p) ⟶ H) → M.ι → J → PadicAlgCl p := fun x l i =>
    valR x (LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l) ((t i).f fun _ => l)
  have wl : ∀ l i, H.basicOpen ((t i).f fun _ => l) ≤ M.U l := fun l i =>
    (H.basicOpen_le _).trans (LB.wchart_le M (fun _ : Fin 1 => 𝟙 H) (fun _ => l) 0)
  have wne : ∀ {x : Sp (PadicAlgCl p) ⟶ H} {l i}, ⊤ ≤ x ⁻¹ᵁ H.basicOpen ((t i).f fun _ => l) → w x l i ≠ 0 :=
    fun h => ((isUnit_valR_iff _ _ (fun _ hz => H.basicOpen_le _ (h hz)) _).2 h).ne_zero
  have hv : ∀ x m m', ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m' → ∀ i,
      (b.map σ).mulVec (v x m) i = tv L (x ≫ ψ' ≫ π) m m' ^ N * (b.map σ).mulVec (v x m') i := by
    intro x m m' hm hm' i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e := (sec_val (s k) (x := x ≫ ψ') (i := fun _ => m) (j := fun _ => m') (le_wchart fun _ => hm)
      (le_wchart fun _ => hm')).trans (congrArg (· * _) (tv_linComb L _ _ (fun _ => hm) fun _ => hm'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.assoc] at e
    rw [mul_left_comm]
    exact congrArg _ e
  have hw : ∀ x l l', ⊤ ≤ x ⁻¹ᵁ M.U l → ⊤ ≤ x ⁻¹ᵁ M.U l' → ∀ i, w x l i = tv M x l l' ^ N * w x l' i := by
    intro x l l' hl hl' i
    have e := (sec_val (t i) (x := x) (i := fun _ => l) (j := fun _ => l') (le_wchart fun _ => hl)
      (le_wchart fun _ => hl')).trans (congrArg (· * _) (tv_linComb M _ _ (fun _ => hl) fun _ => hl'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.comp_id] at e
    exact e
  have key : ∀ x l m, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m →
      ∃ c : PadicAlgCl p, c ≠ 0 ∧ ∀ i, (b.map σ).mulVec (v x m) i = c * w (x ≫ j) l i := by
    intro x l m hx hl hm
    have h₁ := hlink x (v x m) hx ⟨fun _ => m, 1, le_wchart fun _ => hm, fun i => (_root_.one_mul _).symm⟩
    obtain ⟨c, hc⟩ := crd_unique (s := t) (x := x ≫ j) (v := w (x ≫ j) l)
      ⟨fun _ => l, 1, fun _ hz => Set.mem_iInter.2 fun _ => hl hz, fun i => (_root_.one_mul _).symm⟩ h₁
    exact ⟨c, c.ne_zero, hc⟩
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (J × M.ι) L.ι
    (fun a => H.basicOpen ((t a.1).f fun _ => a.2)) (fun m => (ψ' ≫ π) ⁻¹ᵁ L.U m)
    (fun a m x => (b.map σ).mulVec (v x m) a.1 * ω x a.2 m ^ N * (w (x ≫ j) a.2 a.1)⁻¹)
    (fun z => exists_chart hL _)
    (fun a m => ((Reg.sum fun k => (Reg.const (b a.1 k)).mul (Reg.pull ψ' (U := LB.wchart L (fun _ : Fin 1 => π) fun _ => m)
        (W := j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m)
        (fun _ hz => Set.mem_iInter.2 fun _ => hz.2) ((s k).f fun _ => m))).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m) a.2 m (fun _ hz => wl _ _ hz.1) fun _ hz => hz.2).1).pow _)).mul
      (Reg.inv_basicOpen j _ inf_le_left))
    (fun a m x hx ha hm => by
      obtain ⟨c, hc, e⟩ := key x a.2 m hx (fun _ hz => wl _ _ (ha hz)) hm
      exact mul_ne_zero (mul_ne_zero ((e _).trans_ne (mul_ne_zero hc (wne ha)))
        (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => wl _ _ (ha hz)) hm))) (inv_ne_zero (wne ha)))
    (fun a m m' x _ ha hm hm' => by
      beta_reduce
      rw [hv x m m' hm hm', ← hω.right x a.2 m m' (fun _ hz => wl _ _ (ha hz)) hm hm', mul_pow]
      ring)
    (fun a a' => ⟨1, fun m x hx ha ha' hm => by
      have hl : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a.2 := fun _ hz => wl _ _ (ha hz)
      have hl' : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a'.2 := fun _ hz => wl _ _ (ha' hz)
      obtain ⟨c, -, e⟩ := key x a.2 m hx hl hm
      have h₁ := wne ha
      have h₂ := wne ha'
      beta_reduce
      rw [valR_eq (x ≫ j) (H.basicOpen ((t a.1).f fun _ => a.2) ⊓ H.basicOpen ((t a'.1).f fun _ => a'.2))
        (le_inf ha ha'), Units.val_one, map_one, e, e,
        hw _ a.2 a'.2 hl hl' a'.1, hω.left x a.2 a'.2 m hl hl' hm, mul_pow]
      field_simp⟩)
  refine ⟨κ, hκ, fun c x l m hc hx hq hl hm => ?_⟩
  have hlw : ⊤ ≤ c ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l := fun _ hz => Set.mem_iInter.2 fun _ => hl hz
  obtain ⟨i₀, hi₀⟩ := hprim c _ hc ⟨fun _ => l, 1, hlw, fun i => (_root_.one_mul _).symm⟩
  have hwc : ∀ i, w (x ≫ j) l i = (valR c _ ((t i).f fun _ => l) : OO p) := fun i => by
    rw [hx]
    exact (valR_spMap (OO p).subtype c _ hlw).2 _
  have hle : ∀ i, ‖w (x ≫ j) l i‖ ≤ 1 := fun i => by
    rw [hwc]
    exact (mem_OO_iff _).1 (Subtype.prop _)
  have h1 : ‖w (x ≫ j) l i₀‖ = 1 := by
    obtain ⟨d, hd⟩ := hi₀.exists_right_inv
    have e : w (x ≫ j) l i₀ * (d : PadicAlgCl p) = 1 := by
      rw [hwc]
      exact congrArg Subtype.val hd
    have e' := congrArg norm e
    rw [norm_mul, norm_one] at e'
    exact le_antisymm (hle _) (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  obtain ⟨d, -, e⟩ := key x l m hq (by rw [hx]; exact fun _ _ => hl trivial) hm
  have h₀ := h (i₀, l) m c x hc hx hq ((isUnit_valR_iff _ _ hlw _).1 hi₀) hm
  have hd : ∀ i, ‖(b.map σ).mulVec (v x m) i * ω x l m ^ N‖ = κ * ‖w (x ≫ j) l i‖ := fun i => by
    rw [← h₀]
    simp only [e, norm_mul, norm_inv, h1]
    ring
  refine ⟨⟨i₀, (hd i₀).trans (by rw [h1, _root_.mul_one])⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (hd i).trans_le (mul_le_of_le_one_right hκ.le (hle i))

end GlobalTheory.ZH.FrameNorm
end
end
end
