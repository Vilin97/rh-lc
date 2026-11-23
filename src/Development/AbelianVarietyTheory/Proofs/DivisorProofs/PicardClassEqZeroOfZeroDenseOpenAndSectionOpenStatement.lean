module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTwoOpenCoverUnitsSplit

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPic

open TopologicalSpace

theorem exists_units_of_gen_restrict {Z : Scheme.{0}} (L : LB Z) (O : Z.Opens) (t : LB.Gen (L.pull O.ι))
    (ht : t.IsGen) : ∃ b : ∀ i, Γ(Z, L.U i ⊓ O)ˣ, ∀ (i j : L.ι) (x : Z), x ∈ L.U i → x ∈ L.U j → x ∈ O →
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) = gm (𝟙 Z) x (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Z) x (L.U j ⊓ O) (b j) := by
  choose c hc using fun i : L.ι => exists_ext_unit O.ι ((L.pull O.ι).U (fun _ => i)) (t.s (fun _ => i))
  have le : ∀ i, L.U i ⊓ O ≤ O.ι ''ᵁ ((L.pull O.ι).U (fun _ => i)) := by
    intro i x hx
    have m : (⟨x, hx.2⟩ : O.toScheme) ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hx.1
    exact ⟨⟨x, hx.2⟩, m, rfl⟩
  refine ⟨fun i => res (le i) (c i), fun i j x hi hj hx => ?_⟩
  let z : O.toScheme := ⟨x, hx⟩
  have mi : z ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hi
  have mj : z ∈ (L.pull O.ι).U (fun _ => j) := mem_pull.2 hj
  have hW : O.ι z ∈ L.U i ⊓ L.U j ⊓ O := ⟨⟨hi, hj⟩, hx⟩
  have hWi : O.ι z ∈ L.U i ⊓ O := ⟨hi, hx⟩
  have hWj : O.ι z ∈ L.U j ⊓ O := ⟨hj, hx⟩
  have hWij : O.ι z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have l₁ : L.U i ⊓ L.U j ⊓ O ≤ L.U i ⊓ L.U j := inf_le_left
  have l₂ : L.U i ⊓ L.U j ⊓ O ≤ L.U j ⊓ O := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have key := gm_inj O.ι z (U := L.U i ⊓ O) (U' := L.U i ⊓ L.U j ⊓ O) hWi hW
    (a := res (le i) (c i)) (b := res l₁ (L.g i j) * res l₂ (res (le j) (c j))) (by
      rw [map_mul, gm_res O.ι z l₁ hW, gm_res O.ι z l₂ hW, gm_res O.ι z (le j) hWj, gm_res O.ι z (le i) hWi]
      have e₁ := hc i O.toScheme (𝟙 _) z mi
      have e₂ := hc j O.toScheme (𝟙 _) z mj
      rw [Category.id_comp] at e₁ e₂
      rw [e₁, e₂, (isGen_iff_germ t).1 ht z _ _ mi mj, gm_pull_g L O.ι (𝟙 _) z _ _ mi mj, Category.id_comp])
  rw [map_mul, gm_res (𝟙 Z) (O.ι z) l₁ hW, gm_res (𝟙 Z) (O.ι z) l₂ hW] at key
  exact key

theorem eq_zero_of_pull_eq_zero_of_units_split : ∀ (Z : Scheme.{0}) (O O' : Z.Opens), O ⊔ O' = ⊤ →
    (∀ F : Γ(Z, O ⊓ O')ˣ, ∃ (u : Γ(Z, O)ˣ) (u' : Γ(Z, O')ˣ),
      F = res (inf_le_left : O ⊓ O' ≤ O) u * res (inf_le_right : O ⊓ O' ≤ O') u') →
    ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull O'.ι c = 0 → c = 0 := by
  intro Z O O' hcov hsplit c hc hc'
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  rw [← cls_pull hL O.ι (pull_isLB hL O.ι)] at hc
  rw [← cls_pull hL O'.ι (pull_isLB hL O'.ι)] at hc'
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hc
  obtain ⟨t', ht'⟩ := (cls_eq_zero_iff _).1 hc'
  obtain ⟨b, hb⟩ := exists_units_of_gen_restrict L O t ht
  obtain ⟨b', hb'⟩ := exists_units_of_gen_restrict L O' t' ht'
  have key₁ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y => by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  have key₂ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * y * x⁻¹ = a * y := fun a x y => by
    rw [mul_right_comm, mul_inv_cancel_right]

  let W : L.ι → Z.Opens := fun i => L.U i ⊓ (O ⊓ O')
  have lw : ∀ i, W i ≤ L.U i ⊓ O := fun i => inf_le_inf_left _ inf_le_left
  have lw' : ∀ i, W i ≤ L.U i ⊓ O' := fun i => inf_le_inf_left _ inf_le_right
  let q : ∀ i, Γ(Z, W i)ˣ := fun i => res (lw i) (b i) * (res (lw' i) (b' i))⁻¹
  have gq : ∀ i x, x ∈ W i → gm (𝟙 Z) x (W i) (q i) =
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) * (gm (𝟙 Z) x (L.U i ⊓ O') (b' i))⁻¹ := fun i x hx => by
    simp only [q, map_mul, map_inv, gm_res (𝟙 Z) x (lw i) hx, gm_res (𝟙 Z) x (lw' i) hx]
  obtain ⟨F, hF⟩ := glue_unit (O ⊓ O') W (fun i => inf_le_right) (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact Opens.mem_iSup.2 ⟨i, hi, hx⟩) q (fun i j x hx => by
      rw [gq i x hx.1, gq j x hx.2, hb i j x hx.1.1 hx.2.1 hx.1.2.1, hb' i j x hx.1.1 hx.2.1 hx.1.2.2, key₁])
  obtain ⟨u, u', hu⟩ := hsplit F

  have gF : ∀ i x, x ∈ W i → gm (𝟙 Z) x (L.U i ⊓ O) (b i) =
      gm (𝟙 Z) x (L.U i ⊓ O') (b' i) * gm (𝟙 Z) x O u * gm (𝟙 Z) x O' u' := fun i x hx => by
    have e := congrArg (gm (𝟙 Z) x (W i)) (hF i)
    rw [gm_res (𝟙 Z) x _ hx, gq i x hx, hu, map_mul, gm_res (𝟙 Z) x _ hx.2, gm_res (𝟙 Z) x _ hx.2] at e
    rw [(mul_inv_eq_iff_eq_mul).1 e.symm]
    ac_rfl

  have loc : ∀ i, ∃ s : Γ(Z, L.U i)ˣ,
      (∀ y, y ∈ L.U i → y ∈ O → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹) ∧
      (∀ y, y ∈ L.U i → y ∈ O' → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u') := by
    intro i
    let V : Bool → Z.Opens := fun β => Bool.rec (L.U i ⊓ O') (L.U i ⊓ O) β
    let v : ∀ β, Γ(Z, V β)ˣ := fun β => Bool.rec (motive := fun β => Γ(Z, V β)ˣ)
      (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) β
    have hV : ∀ β, V β ≤ L.U i := fun β => by cases β <;> exact inf_le_left
    have g₁ : ∀ y, y ∈ L.U i ⊓ O → gm (𝟙 Z) y (V true) (v true) =
        gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹ := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O) (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) = _
      rw [map_mul, map_inv, gm_res (𝟙 Z) y _ hy]
    have g₀ : ∀ y, y ∈ L.U i ⊓ O' → gm (𝟙 Z) y (V false) (v false) =
        gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u' := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O') (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') = _
      rw [map_mul, gm_res (𝟙 Z) y _ hy]
    obtain ⟨s, hs⟩ := glue_unit (L.U i) V hV (fun y hy => by
        have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
        rcases Opens.mem_sup.1 h with h | h
        · exact Opens.mem_iSup.2 ⟨true, hy, h⟩
        · exact Opens.mem_iSup.2 ⟨false, hy, h⟩) v (fun β β₂ y hy => by
        cases β <;> cases β₂
        · rfl
        · rw [g₀ y hy.1, g₁ y hy.2, gF i y ⟨hy.1.1, hy.2.2, hy.1.2⟩, key₂]
        · rw [g₁ y hy.1, g₀ y hy.2, gF i y ⟨hy.1.1, hy.1.2, hy.2.2⟩, key₂]
        · rfl)
    refine ⟨s, fun y hi ho => ?_, fun y hi ho => ?_⟩
    · have e := congrArg (gm (𝟙 Z) y (V true)) (hs true)
      rw [gm_res (𝟙 Z) y (hV true) (show y ∈ L.U i ⊓ O from ⟨hi, ho⟩)] at e
      exact e.trans (g₁ y ⟨hi, ho⟩)
    · have e := congrArg (gm (𝟙 Z) y (V false)) (hs false)
      rw [gm_res (𝟙 Z) y (hV false) (show y ∈ L.U i ⊓ O' from ⟨hi, ho⟩)] at e
      exact e.trans (g₀ y ⟨hi, ho⟩)
  choose s hs using loc
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, (isGen_iff_germ _).2 fun y i j hi hj => ?_⟩
  have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
  rcases Opens.mem_sup.1 h with h | h
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).1 y hi h, (hs j).1 y hj h, hb i j y hi hj h, _root_.mul_assoc]
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).2 y hi h, (hs j).2 y hj h, hb' i j y hi hj h, _root_.mul_assoc]

end GlobalTheory.CechPic
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTwoOpenCoverUnitsSplitStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechPicard_eq_zero_of_twoOpen_cover_units_split : ∀ (Z : Scheme.{0}) (O O' : Z.Opens), O ⊔ O' = ⊤ → (∀ F : Γ(Z, O ⊓ O')ˣ, ∃ (u : Γ(Z, O)ˣ) (u' : Γ(Z, O')ˣ), F = res (inf_le_left : O ⊓ O' ≤ O) u * res (inf_le_right : O ⊓ O' ≤ O') u') → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull O'.ι c = 0 → c = 0 := by
  first | exact @GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split | exact GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split | (intros; apply GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAboveDenseOpenEqGlobalMulPullback

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.UnitAboveOpen

theorem exists_extend (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T]
    (hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T) (U : T.Opens) (hU : (U : Set T).Nonempty)
    (p : H ⟶ T) (e : T ⟶ H) (hs : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _)
    (F : Γ(H, p ⁻¹ᵁ U)ˣ) (hF : ∀ y : U.toScheme, gm (U.ι ≫ e) y (p ⁻¹ᵁ U) F = 1) :
    ∃ G : Γ(H, ⊤)ˣ, F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G := by
  have : Nonempty U.toScheme := ⟨⟨hU.some, hU.some_mem⟩⟩
  have : IsIntegral H := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have hP : IsPullback (p ⁻¹ᵁ U).ι (p ∣_ U) p U.ι := (isPullback_morphismRestrict p U).flip
  let eU : U.toScheme ⟶ (p ⁻¹ᵁ U).toScheme := hP.lift (U.ι ≫ e) (𝟙 _) (by simp [he])
  have heU : eU ≫ (p ⁻¹ᵁ U).ι = U.ι ≫ e := hP.lift_fst _ _ _
  have : Nonempty (p ⁻¹ᵁ U).toScheme := ⟨eU (Nonempty.some inferInstance)⟩
  let L : LB H := ⟨PUnit, fun _ ↦ ⊤, fun _ _ ↦ 1⟩
  have hL : L.IsLB := ⟨by simp [L], fun _ ↦ map_one _, fun _ _ _ ↦ by simp [L]⟩
  let φ : PEmpty → (H ⟶ H) := PEmpty.elim
  let ε : PEmpty → ℤ := PEmpty.elim
  have hw {Y : Scheme.{0}} (ψ : PEmpty → (Y ⟶ H)) (a) (y : Y) : y ∈ LB.wchart L ψ a :=
    Set.mem_iInter.2 fun k ↦ k.elim
  have hm (y : (p ⁻¹ᵁ U).toScheme) : (p ⁻¹ᵁ U).ι y ∈ p ⁻¹ᵁ U := y.2
  let t : LB.Gen (LB.LinComb L (fun i ↦ (p ⁻¹ᵁ U).ι ≫ φ i) ε) :=
    ⟨fun a ↦ res (fun y _ ↦ hm y) (pullU (p ⁻¹ᵁ U).ι _ F)⟩
  have htg {Z : Scheme.{0}} (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (z : Z) (a) :
      gm r z (LB.wchart L (fun i ↦ (p ⁻¹ᵁ U).ι ≫ φ i) a) (t.s a) =
        gm (r ≫ (p ⁻¹ᵁ U).ι) z (p ⁻¹ᵁ U) F :=
    (gm_res r z _ (hw _ _ _) _).trans (gm_pull r _ z _ (hm _) F)
  let ρ : LB.Gen (LB.LinComb L (fun i ↦ e ≫ φ i) ε) := ⟨fun a ↦ 1⟩
  have ht : t.IsGen := fun a b ↦ by
    obtain rfl : a = b := funext fun k ↦ PEmpty.elim k
    simp [LB.LinComb]
  have hρ : ρ.IsGen := fun a b ↦ by
    obtain rfl : a = b := funext fun k ↦ PEmpty.elim k
    simp [LB.LinComb]
  have hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ U.ι) := by
    intro a b _ _ _
    refine unit_ext fun y hy ↦ ?_
    rw [gm_res _ y _ hy, gm_res _ y _ hy]
    refine Eq.trans (b := 1) ((gm_res _ y _ (hw _ _ _) _).trans
      ((gm_pull _ _ y _ (hw _ _ _) _).trans ((htg _ _ _).trans ?_))) ?_
    · rw [Category.id_comp, heU, hF]
    · refine Eq.symm ((gm_res _ y _ (hw _ _ _) _).trans ((gm_pull _ _ y _ (hw _ _ _) _).trans ?_))
      exact map_one _
  obtain ⟨c, ⟨-, hc'⟩, -⟩ := GlobalTheory.GenExtendNormal.existsUnique_gen_extend T hT U.toScheme H
    (p ⁻¹ᵁ U).toScheme H U.ι p e (p ⁻¹ᵁ U).ι (p ∣_ U) eU hs hg he hP heU L hL PEmpty φ ε t ρ
    ht hρ hc
  let a : PEmpty → L.ι := PEmpty.elim
  refine ⟨res (fun y _ ↦ hw φ a y : (⊤ : H.Opens) ≤ LB.wchart L φ a) (c.s a),
    GlobalTheory.GenExtendNormal.unit_ext_of_isOpenImmersion (p ⁻¹ᵁ U).ι fun y hy ↦ ?_⟩
  rw [gm_res _ y _ hy, gm_res (p ⁻¹ᵁ U).ι y (V := ⊤) _ trivial]
  have h₁ := htg (𝟙 _) y a
  rw [← hc', Category.id_comp] at h₁
  rw [← h₁]
  exact (gm_res _ y _ (hw _ _ _) _).trans ((gm_pull _ _ y _ (hw _ _ _) _).trans
    (by rw [Category.id_comp]))

theorem exists_eq_res_mul_pullU :
    ∀ (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : H ⟶ T) (e : T ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ F : Γ(H, p ⁻¹ᵁ U)ˣ, ∃ (G : Γ(H, ⊤)ˣ) (w : Γ(T, U)ˣ), F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G * pullU p U w := by
  intro T H _ _ hT U hU p e hs hg he F
  have hle : U ≤ e ⁻¹ᵁ p ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, he]; rfl
  let w : Γ(T, U)ˣ := res hle (pullU e _ F)
  obtain ⟨G, hG⟩ := exists_extend T H hT U hU p e hs hg he (F * (pullU p U w)⁻¹) fun y ↦ by
    have hy : U.ι y ∈ U := y.2
    have hy' : p ((U.ι ≫ e) y) ∈ U := hle hy
    rw [map_mul, map_inv, gm_pull _ p y U hy', Category.assoc, he, Category.comp_id,
      gm_res _ y hle hy, gm_pull _ e y _ (hle hy), mul_inv_cancel]
  exact ⟨G, w, by rw [← hG, inv_mul_cancel_right]⟩

end GlobalTheory.UnitAboveOpen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAboveDenseOpenEqGlobalMulPullbackStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unit_above_dense_open_eq_global_mul_pullback : ∀ (T H : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : H ⟶ T) (e : T ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ F : Γ(H, p ⁻¹ᵁ U)ˣ, ∃ (G : Γ(H, ⊤)ˣ) (w : Γ(T, U)ˣ), F = res (le_top : p ⁻¹ᵁ U ≤ ⊤) G * pullU p U w := by
  first | exact @GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU | exact GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU | (intros; apply GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroOfZeroDenseOpenAndSectionOpen

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_appLE_ι {Z : Scheme.{0}} (O W : Z.Opens) (hW : W ≤ O) (W' : O.toScheme.Opens)
    (h : W' = O.ι ⁻¹ᵁ W) : Function.Bijective (O.ι.appLE W W' h.le) := by
  subst h
  have : IsIso (O.ι.app W) := Scheme.Hom.isIso_app _ _ (by simpa using hW)
  rw [← Scheme.Hom.app_eq_appLE]
  exact ConcreteCategory.bijective_of_isIso _

theorem eq_zero_of_pull_eq_zero : ∀ (T Z : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : Z ⟶ T) (O : Z.Opens) (e : T ⟶ O.toScheme), Smooth (O.ι ≫ p) → GeometricallyIntegral (O.ι ≫ p) → e ≫ O.ι ≫ p = 𝟙 _ → O ⊔ p ⁻¹ᵁ U = ⊤ → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull (p ⁻¹ᵁ U).ι c = 0 → c = 0 := by
  intro T Z _ _ hT U hU p O e hs hg he hcov
  refine GlobalTheory.T.cechPicard_eq_zero_of_twoOpen_cover_units_split Z O (p ⁻¹ᵁ U) hcov fun F => ?_
  have h1 : (O.ι ≫ p) ⁻¹ᵁ U = O.ι ⁻¹ᵁ (O ⊓ p ⁻¹ᵁ U) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq, Scheme.Hom.comp_preimage]
  have h2 : (⊤ : O.toScheme.Opens) = O.ι ⁻¹ᵁ O := by simp
  have b1 := bijective_appLE_ι O (O ⊓ p ⁻¹ᵁ U) inf_le_left _ h1
  have b2 := bijective_appLE_ι O O le_rfl _ h2
  obtain ⟨G, w, hGw⟩ := GlobalTheory.T.unit_above_dense_open_eq_global_mul_pullback T O hT U hU (O.ι ≫ p) e hs hg he
    (Units.map (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom.toMonoidHom F)
  let ε := RingEquiv.ofBijective (O.ι.appLE O ⊤ h2.le).hom b2
  refine ⟨Units.map ε.symm.toMonoidHom G, pullU p U w, ?_⟩
  apply Units.ext
  apply b1.1
  have hv := congrArg Units.val hGw
  have hG : (O.ι.appLE O ⊤ h2.le).hom (ε.symm G) = G := ε.apply_symm_apply _
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F =
    O.toScheme.presheaf.map (homOfLE le_top).op (G : Γ(O, ⊤)) * (O.ι ≫ p).app U (w : Γ(T, U)) at hv
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F = (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom
    (Z.presheaf.map (homOfLE inf_le_left).op (ε.symm G) *
      Z.presheaf.map (homOfLE inf_le_right).op (p.app U (w : Γ(T, U))))
  rw [hv, map_mul, ← hG]
  congr 1
  · rw [hG]
    conv_lhs => rw [← hG]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.PicGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroOfZeroDenseOpenAndSectionOpenStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.picardClass_eq_zero_of_zero_dense_open_and_section_open : ∀ (T Z : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : Z ⟶ T) (O : Z.Opens) (e : T ⟶ O.toScheme), Smooth (O.ι ≫ p) → GeometricallyIntegral (O.ι ≫ p) → e ≫ O.ι ≫ p = 𝟙 _ → O ⊔ p ⁻¹ᵁ U = ⊤ → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull (p ⁻¹ᵁ U).ι c = 0 → c = 0 := by
  first | exact @GlobalTheory.PicGlue.eq_zero_of_pull_eq_zero | exact GlobalTheory.PicGlue.eq_zero_of_pull_eq_zero | (intros; apply GlobalTheory.PicGlue.eq_zero_of_pull_eq_zero <;> assumption)
end
end
