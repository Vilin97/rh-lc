module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfFiniteFibres
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFlagEqOfPluckerPointsEqFieldPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfFiniteFibres
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsOfPulledBackLineBundlesOnFramesStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassGradedTensorBundleFinsetSum

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem cls_LL_add (F : FlagMod.Frames Y π) (e e' : Ix Dw → ℤ) :
    GlobalTheory.CechPic.cls (F.LL (e + e')) (F.isLB_LL _) =
      GlobalTheory.CechPic.cls (F.LL e) (F.isLB_LL _) + GlobalTheory.CechPic.cls (F.LL e') (F.isLB_LL _) := by
  have h := GlobalTheory.CechPic.isLB_tens (F.isLB_LL e) (F.isLB_LL e')
  refine ((GlobalTheory.CechPic.cls_eq_iff (F.isLB_LL (e + e')) h).2 (GlobalTheory.CechPic.iso_of_chart h ⟨fun k => (k, k), fun _ _ h => ⟨h, h⟩, ?_⟩)).trans
    (GlobalTheory.CechPic.cls_tens _ _ h)
  intro y p q hp hq
  refine Eq.trans ?_ (GlobalTheory.CechPic.gm_tens (F.LL e) (F.LL e') (𝟙 Z) y (p, p) (q, q) ⟨hp, hp⟩ ⟨hq, hq⟩).symm
  exact (congrArg (gm (𝟙 Z) y _) (F.LL_add_g e e' p q)).trans (map_mul _ _ _)

def clsLLHom (F : FlagMod.Frames Y π) : (Ix Dw → ℤ) →+ GlobalTheory.CechPic.Pic Z :=
  AddMonoidHom.mk' (fun e => GlobalTheory.CechPic.cls (F.LL e) (F.isLB_LL _)) (cls_LL_add F)

theorem cls_LL_sum (F : FlagMod.Frames Y π) {ι : Type} (s : Finset ι) (e : ι → Ix Dw → ℤ) :
    GlobalTheory.CechPic.cls (F.LL (∑ i ∈ s, e i)) (F.isLB_LL _) = ∑ i ∈ s, GlobalTheory.CechPic.cls (F.LL (e i)) (F.isLB_LL _) :=
  map_sum (clsLLHom F) e s

end GlobalTheory.FlagPlucker
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassGradedTensorBundleFinsetSumStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

theorem _root_.GlobalTheory.T.cechPicardClass_gradedTensorBundle_finset_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {ι : Type} (s : Finset ι) (e : ι → Ix Dw → ℤ), GlobalTheory.CechPic.cls (F.LL (∑ i ∈ s, e i)) (F.isLB_LL _) = ∑ i ∈ s, GlobalTheory.CechPic.cls (F.LL (e i)) (F.isLB_LL _) := by
  first | exact @GlobalTheory.FlagPlucker.cls_LL_sum | exact GlobalTheory.FlagPlucker.cls_LL_sum | (intros; apply GlobalTheory.FlagPlucker.cls_LL_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsSectionsInverseDetFlagBundle

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

theorem det_submatrix_mul_tri {R : Type} [CommRing R] {n p m : ℕ} (A : Matrix (Fin n) (Fin p) R)
    (B : Matrix (Fin p) (Fin p) R) (hB : B.BlockTriangular id) (h : m + 1 ≤ p) (r : Fin (m + 1) → Fin n) :
    ((A * B).submatrix r (Fin.castLE h)).det =
      (A.submatrix r (Fin.castLE h)).det * ∏ i : Fin (m + 1), B (Fin.castLE h i) (Fin.castLE h i) := by
  have e : (A * B).submatrix r (Fin.castLE h) =
      A.submatrix r (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
    ext i l
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun b hb => ?_) (fun _ => rfl)
    have : ¬ (b : ℕ) < m + 1 := fun hb' => hb ⟨⟨b, hb'⟩, rfl⟩
    have h0 : B b (Fin.castLE h l) = 0 := hB (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le l.2 (not_lt.1 this)))
    rw [h0, mul_zero]
  rw [e, Matrix.det_mul, Matrix.det_of_upperTriangular (M := B.submatrix (Fin.castLE h) (Fin.castLE h))]
  · rfl
  · intro i l hil
    exact hB (show Fin.castLE h l < Fin.castLE h i from hil)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem plkU_map_ev (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) {S : Type} [CommRing S]
    (w : Sp S ⟶ Z) (h : ⊤ ≤ w ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)) (hk : ⊤ ≤ w ⁻¹ᵁ F.U k) (hx : ⊤ ≤ (w ≫ π) ⁻¹ᵁ Mc.U)
    (hx' : ⊤ ≤ (w ≫ π) ⁻¹ᵁ (F.M k).U) :
    (plkU F Mc k σ).map (ev w _ h) =
      (lieBasis Mc (w ≫ π) hx).toMatrix (lieBasis (F.M k).toMChart (w ≫ π) hx') * F.uAt k w hk σ := by
  unfold plkU
  rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map,
    ← chg_map Mc (F.M k).toMChart (w ≫ π) hx hx' (le_preimage_inf hx hx')]
  congr 1
  · ext i j; exact ev_appLE w π _ h _ _
  · ext i j; exact ev_res w _ h hk _

theorem plkU_map_ev_chg (F : Frames Y π) (Mc : MChart Y) (k k' : F.J) (σ : E →+* ℂ) {S : Type} [CommRing S]
    (w : Sp S ⟶ Z) (h : ⊤ ≤ w ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)) (h' : ⊤ ≤ w ⁻¹ᵁ (F.U k' ⊓ π ⁻¹ᵁ Mc.U))
    (hh : ⊤ ≤ w ⁻¹ᵁ (F.U k ⊓ F.U k')) :
    (plkU F Mc k' σ).map (ev w _ h') = (plkU F Mc k σ).map (ev w _ h) * (F.B k k' σ).map (ev w _ hh) := by
  have hk := le_preimage_mono inf_le_left hh
  have hk' := le_preimage_mono inf_le_right hh
  have hx : ⊤ ≤ (w ≫ π) ⁻¹ᵁ Mc.U := fun p hp => (h hp).2
  have a := F.inM hk rfl
  have b := F.inM hk' rfl
  rw [plkU_map_ev F Mc k' σ w h' hk' hx b, plkU_map_ev F Mc k σ w h hk hx a,
    ← Module.Basis.toMatrix_mul_toMatrix (lieBasis Mc (w ≫ π) hx) (lieBasis (F.M k).toMChart (w ≫ π) a),
    ← chg_map (F.M k).toMChart (F.M k').toMChart (w ≫ π) a b (le_preimage_inf a b), Matrix.mul_assoc,
    F.chg_uAt k k' w hk hk' hh rfl (le_preimage_inf a b) σ, Matrix.mul_assoc]

open Classical in
theorem prod_zpow_neg_ind {G : Type} [CommGroup G] (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (t : Ix Dw → G) :
    ∏ ix, t ix ^ (-ind σ m ix) = (∏ i : Fin ((m : ℕ) + 1), t (some ⟨σ, Fin.castLE m.2 i⟩))⁻¹ := by
  simp only [zpow_neg, Finset.prod_inv_distrib]
  congr 1
  symm
  refine Fintype.prod_of_injective (fun i : Fin ((m : ℕ) + 1) => (some ⟨σ, Fin.castLE m.2 i⟩ : Ix Dw)) ?_ _
    (fun ix => t ix ^ ind σ m ix) (fun b hb => ?_) (fun i => ?_)
  · intro i i' e
    simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
    exact Fin.castLE_injective _ e
  · rcases b with _ | ⟨τ, j⟩
    · simp [ind]
    · have : ind σ m (some ⟨τ, j⟩) = 0 := by
        simp only [ind, Option.elim]
        rw [if_neg]
        rintro ⟨rfl, hj⟩
        exact hb ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩
      rw [this, zpow_zero]
  · simp [ind, not_lt.2 (Nat.lt_succ_iff.1 i.2)]

theorem plkLoc_sec (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)) :
    ∃ s : ((F.LL (ind σ m)).pull g).Sec, s.f = plkLoc F Mc g hg σ m q := by
  refine ⟨⟨plkLoc F Mc g hg σ m q, fun j j' => ?_⟩, rfl⟩
  unfold plkLoc
  rcases plkIdx Mc m q with _ | r
  · simp
  · refine ext_ev fun S _ z hz => ?_
    have ha := le_preimage_mono inf_le_left hz
    have hb := le_preimage_mono inf_le_right hz
    have h1 := le_preimage_map g (plk_le F Mc g hg (ind σ m) j) ha
    have h2 := le_preimage_map g (plk_le F Mc g hg (ind σ m) j') hb
    have hh : ⊤ ≤ (z ≫ g) ⁻¹ᵁ (F.U (j PUnit.unit) ⊓ F.U (j' PUnit.unit)) :=
      le_preimage_inf (le_preimage_mono inf_le_left h1) (le_preimage_mono inf_le_left h2)
    rw [map_mul, ev_res z _ hz ha, ev_res z _ hz hb, ev_appLE z g _ ha h1, ev_appLE z g _ hb h2,
      ev_pull_g (F.LL (ind σ m)) g j j' z hz hh]
    erw [F.ev_LL_g _ _ _ (z ≫ g) hh]
    unfold plkMinor
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
      ← Matrix.submatrix_map, plkU_map_ev_chg F Mc _ _ σ (z ≫ g) h1 h2 hh,
      det_submatrix_mul_tri (m := (m : ℕ)) _ _ (F.B_map_tri (j PUnit.unit) (j' PUnit.unit) σ (ev (z ≫ g) _ hh)) m.2 r,
      prod_zpow_neg_ind]
    have e : ∏ i : Fin ((m : ℕ) + 1), (F.B (j PUnit.unit) (j' PUnit.unit) σ).map (ev (z ≫ g) _ hh)
        (Fin.castLE m.2 i) (Fin.castLE m.2 i) =
        ((∏ i : Fin ((m : ℕ) + 1), F.TAt (j PUnit.unit) (j' PUnit.unit) (z ≫ g) hh
          (some ⟨σ, Fin.castLE m.2 i⟩) : (S)ˣ) : S) := by
      rw [Units.coe_prod]; rfl
    rw [e, _root_.mul_left_comm, Units.inv_mul, _root_.mul_one]

end GlobalTheory.FlagPlucker

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsSectionsInverseDetFlagBundleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

theorem _root_.GlobalTheory.T.pluckerMinors_sections_inverseDetFlagBundle : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)), ∃ s : ((F.LL (ind σ m)).pull g).Sec, s.f = plkLoc F Mc g hg σ m q := by
  first | exact @GlobalTheory.FlagPlucker.plkLoc_sec | exact GlobalTheory.FlagPlucker.plkLoc_sec | (intros; apply GlobalTheory.FlagPlucker.plkLoc_sec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelWeilFlagModelDetInverseIsAmpleLocal

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.FlagPlucker


open GlobalTheory.FlagMod Formalism.L2.Pj in
theorem isAmpleLB_LL_flagModel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagModel Y) (z : Y.X), ∃ V : Y.X.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB ((X.F.LL (fun ix => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ))).pull (X.π ⁻¹ᵁ V).ι) := by
  intro E _ _ _ H Dw l Xo c Y X z
  have hprop : IsProper X.π := X.proper
  by_cases hz : z ∈ Set.range X.π.base
  · obtain ⟨y, rfl⟩ := hz
    obtain ⟨k0, hk0⟩ := TopologicalSpace.Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ y))
    have hzM : X.π y ∈ (X.F.M k0).U := X.F.le k0 hk0
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVM⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show X.π y ∈ ((X.F.M k0).U : Set Y.X) from hzM) (X.F.M k0).U.isOpen
    refine ⟨V, hzV, hV, ?_⟩
    have hg : ⊤ ≤ ((X.π ⁻¹ᵁ V).ι ≫ X.π) ⁻¹ᵁ (X.F.M k0).toMChart.U := fun p _ => hVM (by
      show X.π ((X.π ⁻¹ᵁ V).ι p) ∈ V
      have : (X.π ⁻¹ᵁ V).ι p ∈ X.π ⁻¹ᵁ V := by
        have h := Scheme.Opens.range_ι (X.π ⁻¹ᵁ V)
        exact (h.le ⟨p, rfl⟩ : _)
      exact this)
    have hf : IsProper ((X.π ∣_ V) ≫ hV.isoSpec.hom) := inferInstance
    choose t ht using fun (p : Σ σ : E →+* ℂ, Fin (Dw.mult σ)) (q : Fin (plkNum (X.F.M k0).toMChart p.2 + 1)) =>
      GlobalTheory.T.pluckerMinors_sections_inverseDetFlagBundle X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg p.1 p.2 q
    have hnz : ∀ p, ⨆ q, nonzeroLocus (t p q) = ⊤ := fun p =>
      GlobalTheory.T.sections_of_pulled_back_line_bundles_on_frames X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg p.1 p.2 (t p) (ht p)
    refine isAmpleLB_of_finite_fibres Γ(Y.X, V) _ ((X.π ∣_ V) ≫ hV.isoSpec.hom) hf (Σ σ : E →+* ℂ, Fin (Dw.mult σ))
      (fun p => (X.F.LL (ind p.1 p.2)).pull (X.π ⁻¹ᵁ V).ι) (fun p => LB.isLB_pull (X.F.isLB_LL _) _)
      (fun p => plkNum (X.F.M k0).toMChart p.2) t hnz ?_ (fun _ => 1) (fun _ => le_rfl) _
      (LB.isLB_pull (X.F.isLB_LL _) _) ?_
    · intro K _ _ a
      have hfin := X.fin K (a ≫ (X.π ⁻¹ᵁ V).ι)
      refine (hfin.preimage (f := fun a' : Sp K ⟶ _ => a' ≫ (X.π ⁻¹ᵁ V).ι)
        fun b _ b' _ e => (cancel_mono _).1 e).subset ?_
      rintro a' ⟨h1, h2⟩
      have e : (X.π ⁻¹ᵁ V).ι ≫ X.π = ((X.π ∣_ V) ≫ hV.isoSpec.hom) ≫ hV.fromSpec := by
        rw [← hV.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
      have hx : a ≫ (X.π ⁻¹ᵁ V).ι ≫ X.π = a' ≫ (X.π ⁻¹ᵁ V).ι ≫ X.π := by
        rw [e]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ hV.fromSpec) h1.symm).trans (Category.assoc _ _ _))
      exact GlobalTheory.T.lieFlag_eq_of_pluckerPoints_eq_field_points X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg (fun σ m => t ⟨σ, m⟩)
        (fun σ m => ht ⟨σ, m⟩) (fun σ m => hnz ⟨σ, m⟩) _ K a a' hx (fun σ m => (h2 ⟨σ, m⟩).symm)
    · have he : (fun ix : Ix Dw => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ)) =
          ∑ p : Σ σ : E →+* ℂ, Fin (Dw.mult σ), ind p.1 p.2 := by
        funext ix
        rcases ix with _ | ⟨σ, i⟩
        · simp [ind]
        · rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single σ]
          · simp only [ind, Option.elim, true_and]
            rw [Finset.sum_boole]
            have : (Finset.univ.filter fun m : Fin (Dw.mult σ) => (i : ℕ) ≤ m) = Finset.Ici i := by
              ext m; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
            simp only [this, Fin.card_Ici]
            push_cast [Nat.cast_sub i.2.le]
            ring
          · intro σ' _ h
            refine Finset.sum_eq_zero fun m _ => ?_
            simp [ind, Ne.symm h]
          · simp
      have h2 : ∀ p : Σ σ : E →+* ℂ, Fin (Dw.mult σ),
          1 • CechPic.cls ((X.F.LL (ind p.1 p.2)).pull (X.π ⁻¹ᵁ V).ι) (LB.isLB_pull (X.F.isLB_LL _) _) =
            CechPic.pull (X.π ⁻¹ᵁ V).ι (CechPic.cls (X.F.LL (ind p.1 p.2)) (X.F.isLB_LL _)) :=
        fun p => one_smul _ _

      rw [CechPic.cls_pull (X.F.isLB_LL _), Finset.sum_congr rfl fun p _ => h2 p, ← map_sum,
      ← GlobalTheory.T.cechPicardClass_gradedTensorBundle_finset_sum X.F Finset.univ (fun p : Σ σ : E →+* ℂ, Fin (Dw.mult σ) => ind p.1 p.2)]
      congr 2
      exact congrArg _ he
  · have hcl : IsClosed (Set.range X.π.base) := X.π.isClosedMap.isClosed_range
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVc⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ (Set.range X.π.base)ᶜ from hz) hcl.isOpen_compl
    refine ⟨V, hzV, hV, ?_⟩
    haveI : IsEmpty (X.π ⁻¹ᵁ V).toScheme := ⟨fun p => hVc p.2 ⟨p.1, rfl⟩⟩
    haveI : IsAffine (X.π ⁻¹ᵁ V).toScheme := isAffine_of_isEmpty
    exact isAmpleLB_of_isAffine (LB.isLB_pull (X.F.isLB_LL _) _)

end GlobalTheory.FlagPlucker

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelWeilFlagModelDetInverseIsAmpleLocalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.borelWeil_flagModel_detInverse_isAmple_local : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagModel Y) (z : Y.X), ∃ V : Y.X.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB ((X.F.LL (fun ix => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ))).pull (X.π ⁻¹ᵁ V).ι) := by
  first | exact @GlobalTheory.FlagPlucker.isAmpleLB_LL_flagModel | exact GlobalTheory.FlagPlucker.isAmpleLB_LL_flagModel | (intros; apply GlobalTheory.FlagPlucker.isAmpleLB_LL_flagModel <;> assumption)
end
end
