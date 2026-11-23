module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueWeightDecompositionRaynaudAffineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPartStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionOfBasicOpens

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtLocal

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open GlobalTheory.TorusModel (isPull_iff)

theorem gm_comp' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  refine Units.ext ?_
  rw [← gs_unit (r ≫ q) z U h, ← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h,
    Category.id_comp, gs_unit q (r z) U h]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem isWt_of_local (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V))
    (h : ∀ (S : Type) [CommRing S] [IsLocalRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ),
      ⊤ ≤ x.left ⁻¹ᵁ V → ⊤ ≤ x'.left ⁻¹ᵁ V → x' ≫ Y.q = x ≫ Y.q →
      (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) →
      valR (A := S) x'.left V f = c α * valR (A := S) x.left V f) : IsWt Y α V f := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun P hP => (map_sub _ _ _).trans (sub_eq_zero.2 ?_))
  let l := algebraMap S (Localization.AtPrime P)
  let k : Over.mk (spMap (l.comp φ)) ⟶ Over.mk (spMap φ) := Over.homMk (spMap l)
    (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom l)).symm
  obtain ⟨a₁, a₂⟩ := valR_spMap l x.left V hV
  obtain ⟨b₁, b₂⟩ := valR_spMap l x'.left V hV'
  have := h _ (l.comp φ) (k ≫ x) (k ≫ x') (fun χ => Units.map l.toMonoidHom (c χ)) a₁ b₁
    (by rw [Category.assoc, Category.assoc, hq]) fun χ y J hJ => by
      have hJ' : Good Q.P.L (k.left y) fun ψ => J (k.left ≫ ψ) := fun ψ => hJ (k.left ≫ ψ)
      have key : ∀ u : Over.mk (spMap φ) ⟶ Y.H, val ((Y.Φ _ (k ≫ u)).s χ) (𝟙 _) y J =
          Units.map (k.left.stalkMap y).hom.toMonoidHom
            (val ((Y.Φ _ u).s χ) (𝟙 _) (k.left y) fun ψ => J (k.left ≫ ψ)) := fun u => by
        refine (((isPull_iff _ _ _).1 (Y.rep.1 _ _ k u)).2 χ y J hJ).trans ?_
        rw [val_of _ (𝟙 _) _ _ (fun i => J (k.left ≫ DegPre.gtφT Q _ (Y.Φ _ u).b χ i)) (fun i => by rw [Category.id_comp])]
        refine Eq.trans ?_ (gm_comp' k.left (𝟙 _) y _ (hJ.mem _ k.left) _)
        rw [Category.comp_id]
        rfl
      rw [key, key, hc χ _ _ hJ', map_mul, ← gm_comp' k.left (𝟙 _) y ⊤ trivial]
      congr 1
      refine Units.ext ?_
      rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
      refine congrArg ((Sp (Localization.AtPrime P)).presheaf.germ ⊤ y trivial).hom ?_
      exact (congrArg (fun q => q.hom (c χ : S)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom l))).symm
  rw [map_mul]
  exact (b₂ f).symm.trans (this.trans (congrArg (_ * ·) (a₂ f)))

end GlobalTheory.Heat.WtLocal

namespace GlobalTheory.Heat.WtLocal

open GlobalTheory.ZH.CrdCalc (valR_res)

theorem isWt_of_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V')), (∀ (g : Γ(Q.P.A.left, V.1)) (h : Q.P.A.left.basicOpen g ≤ V'), IsWt Y α (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) (resG Y.H.left (Y.q.left.preimage_mono h) f)) → IsWt Y α (Y.q.left ⁻¹ᵁ V') f := by
  intro R _ _ Q O _ _ _ oa Y V V' hV α f hf
  refine isWt_of_local Y α _ _ fun S _ _ φ x x' c hx hx' hq hc => ?_
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg (fun q => q.left) hq
  have hp : Y.q.left (x'.left (closedPoint S)) ∈ V' := hx' trivial
  obtain ⟨g, hg, hpg⟩ := V.2.exists_basicOpen_le ⟨_, hp⟩ (hV hp)
  have m' : ⊤ ≤ x'.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of S) x'.left hpg).ge
  have m : ⊤ ≤ x.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) := by
    rw [← Scheme.Hom.comp_preimage, ← e]; exact m'
  have t := hf g hg S φ x x' c _ _ rfl rfl m m' hq hc
  exact (valR_res (R := S) x'.left _ m' f).symm.trans (t.trans (congrArg (_ * ·) (valR_res (R := S) x.left _ m f)))

end GlobalTheory.Heat.WtLocal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionOfBasicOpensStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_of_basicOpens : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V')), (∀ (g : Γ(Q.P.A.left, V.1)) (h : Q.P.A.left.basicOpen g ≤ V'), IsWt Y α (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) (resG Y.H.left (Y.q.left.preimage_mono h) f)) → IsWt Y α (Y.q.left ⁻¹ᵁ V') f := by
  first | exact @GlobalTheory.Heat.WtLocal.isWt_of_basicOpen | exact GlobalTheory.Heat.WtLocal.isWt_of_basicOpen | (intros; apply GlobalTheory.Heat.WtLocal.isWt_of_basicOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimages

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtSub

theorem valR_resG' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  simp only [valR, dif_pos h, dif_pos h']
  congr 1
  change (X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f = _
  rw [Scheme.Hom.map_appLE]

theorem valR_one' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valR x U (1 : Γ(X, U)) = 1 := by
  simp only [valR, dif_pos h, map_one]

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem isWt_res {α : Q.X} {U V : Y.H.left.Opens} (e : V ≤ U) {f : Γ(Y.H.left, U)} (hf : IsWt Y α U f) :
    IsWt Y α V (resG Y.H.left e f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have hU : ⊤ ≤ a ⁻¹ᵁ U := hV.trans (a.preimage_mono e)
  have hU' : ⊤ ≤ a' ⁻¹ᵁ U := hV'.trans (a'.preimage_mono e)
  rw [valR_resG' a' e hV', valR_resG' a e hV]
  exact hf S φ x x' c a a' ha ha' hU hU' hq hc

theorem isWt_inv {V : Y.H.left.Opens} (u : Γ(Y.H.left, V)ˣ) (hu : IsWt Y 0 V u.val) :
    IsWt Y 0 V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have hc0 : c 0 = 1 := WtAlg.c_zero x x' c hc
  have e1 := hu S φ x x' c a a' ha ha' hV hV' hq hc
  rw [hc0, Units.val_one, _root_.one_mul] at e1
  rw [hc0, Units.val_one, _root_.one_mul]
  have m : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V →
      valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val * valR b V u.val = 1 := by
    intro b hb
    rw [← WtAlg.valR_mul'' b V hb, Units.inv_mul, valR_one' b V hb]
  have m' : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V →
      valR b V u.val * valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val = 1 := by
    intro b hb
    rw [← WtAlg.valR_mul'' b V hb, Units.mul_inv, valR_one' b V hb]
  calc valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val
        = valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val *
            (valR a V u.val * valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val) := by rw [m' a hV, _root_.mul_one]
    _ = (valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val * valR a' V u.val) *
            valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by rw [e1, _root_.mul_assoc]
    _ = valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by rw [m a' hV', _root_.one_mul]

theorem isRaynaudTorusWeightFunction_zero_pow {V : Y.H.left.Opens} {g : Γ(Y.H.left, V)} (hg : IsWt Y 0 V g) (n : ℕ) : IsWt Y 0 V (g ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    have h1 := WtAlg.isWt_natCast (Y := Y) V 1
    rwa [Nat.cast_one] at h1
  | succ n ih =>
    rw [pow_succ']
    exact WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hg ih

end GlobalTheory.Heat.WtSub

namespace GlobalTheory.Heat.WtSub

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

theorem isWt_basicOpen (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left)
    (hd : IsField (Y.q.left ⁻¹ᵁ V.1) d)
    (hpres : ∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f))
    (hdec : ∀ (W : Q.P.A.left.Opens), IsAffineOpen W → ∀ f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W),
      ∃! F : Q.X →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), (∀ χ, IsWt Y χ _ (F χ)) ∧ f = F.sum (fun _ t => t))
    (hP : IsAffineOpen (Y.q.left ⁻¹ᵁ V.1))
    (g : Γ(Q.P.A.left, V.1)) (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g))
    (hf : IsWt Y α _ f) : IsWt Y α _ (d _ f) := by
  have hle : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g ≤ Y.q.left ⁻¹ᵁ V.1 :=
    Y.q.left.preimage_mono (Q.P.A.left.basicOpen_le g)
  set G : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) := (Y.q.left.app V.1).hom g with hGdef
  have hG0 : IsWt Y 0 _ G := AbConst.isWt_app Y V.1 g
  have heq : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g = Y.H.left.basicOpen G :=
    Scheme.preimage_basicOpen Y.q.left g
  let _ : Algebra Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    (Y.H.left.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : IsLocalization.Away G Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    hP.isLocalization_of_eq_basicOpen G (homOfLE hle) heq
  have halg : ∀ t, algebraMap Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)
      Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) t = resG Y.H.left hle t := fun _ => rfl
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj G f
  rw [← map_pow, halg, halg] at ha
  have hunit : IsUnit (resG Y.H.left hle (G ^ n)) := by
    rw [← halg, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit G).pow n
  have hGn0 : IsWt Y 0 _ (resG Y.H.left hle (G ^ n)) := isWt_res hle (isRaynaudTorusWeightFunction_zero_pow hG0 n)
  obtain ⟨F, ⟨hFw, hFa⟩, -⟩ := hdec V.1 V.2 a
  obtain ⟨F0, -, huniq⟩ := hdec (Q.P.A.left.basicOpen g) (V.2.basicOpen g) (f * resG Y.H.left hle (G ^ n))
  have hA : Finsupp.mapRange (resG Y.H.left hle) (map_zero _) F = F0 := by
    refine huniq _ ⟨fun χ => ?_, ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact isWt_res hle (hFw χ)
    · rw [Finsupp.sum_mapRange_index (fun _ => rfl), ha, hFa, map_finsuppSum]
  have hB : Finsupp.single α (f * resG Y.H.left hle (G ^ n)) = F0 := by
    refine huniq _ ⟨fun χ => ?_, ?_⟩
    · by_cases hχ : α = χ
      · subst hχ
        rw [Finsupp.single_eq_same, _root_.mul_comm]
        exact WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hGn0 hf
      · rw [Finsupp.single_eq_of_ne' hχ]
        exact WtAlg.isWt_zero _ _
    · rw [Finsupp.sum_single_index rfl]
  have hα : resG Y.H.left hle (F α) = f * resG Y.H.left hle (G ^ n) := by
    have h1 := DFunLike.congr_fun (hA.trans hB.symm) α
    rwa [Finsupp.mapRange_apply, Finsupp.single_eq_same] at h1
  obtain ⟨-, hmul, hres⟩ := hd
  have hdfG : IsWt Y α _ (d _ (f * resG Y.H.left hle (G ^ n))) := by
    rw [← hα, hres _ _ hle le_rfl]
    exact isWt_res hle (hpres α (F α) (hFw α))
  have hdG : IsWt Y 0 _ (d _ (resG Y.H.left hle (G ^ n))) := by
    rw [hres _ _ hle le_rfl]
    exact isWt_res hle (hpres 0 (G ^ n) (isRaynaudTorusWeightFunction_zero_pow hG0 n))
  have hGdf : IsWt Y α _ (resG Y.H.left hle (G ^ n) * d _ f) := by
    have e2 : resG Y.H.left hle (G ^ n) * d _ f =
        d _ (f * resG Y.H.left hle (G ^ n)) - f * d _ (resG Y.H.left hle (G ^ n)) := by
      rw [hmul _ hle]
      ring
    rw [e2, _root_.mul_comm f (d _ (resG Y.H.left hle (G ^ n)))]
    exact WtAlg.isWt_sub hdfG (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hdG hf)
  obtain ⟨u, hu⟩ := hunit
  have hu0 : IsWt Y 0 _ (u⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g)ˣ).val := by
    refine isWt_inv u ?_
    rw [hu]
    exact hGn0
  have h2 := WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hu0 hGdf
  rwa [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul] at h2

end GlobalTheory.Heat.WtSub

namespace GlobalTheory.Heat.WtSub

theorem isWt_field_of_le : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V.1) d → (∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f)) → ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  intro R _ _ Q O _ _ _ oa Y V d hd hpres α V' hV' f hf
  apply GlobalTheory.T.isRaynaudTorusWeightFunction_of_basicOpens R Q O oa Y V V' hV' α (d _ f)
  intro g hg
  have hle : Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V.1 := Y.q.left.preimage_mono hV'
  obtain ⟨hadd, hmul, hres⟩ := hd
  rw [← hres _ _ (Y.q.left.preimage_mono hg) hle f]
  exact isWt_basicOpen Y V d ⟨hadd, hmul, hres⟩ hpres (fun W hW => GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine R Q O oa Y W hW)
    (GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart R Q O oa Y V) g α _ (isWt_res _ hf)

end GlobalTheory.Heat.WtSub
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimagesStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.weight_preserving_vectorField_on_smaller_preimages : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V.1) d → (∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f)) → ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  first | exact @GlobalTheory.Heat.WtSub.isWt_field_of_le | exact GlobalTheory.Heat.WtSub.isWt_field_of_le | (intros; apply GlobalTheory.Heat.WtSub.isWt_field_of_le <;> assumption)
end
end
