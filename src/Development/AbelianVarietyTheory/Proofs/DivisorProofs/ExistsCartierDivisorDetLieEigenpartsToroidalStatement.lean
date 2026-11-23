module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpacePullbackEigenDeterminantDivisorEqGradedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameCoordinatesLocallyConstantUpToUnits

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.FrameSpread

open GlobalTheory.Toroidal (gen genι genStr)
open GlobalTheory.ShFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {F : EigFrame Z φ x}
    {F' : EigFrame Z φ' x'} {F'' : EigFrame Z φ'' x''} {a : R →+* R'} {b : R' →+* R''} (h1 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) a F')
    (h2 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) (b.comp a) F'') : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F' embτ basisIdx) b F'' := fun τ i => by
  rw [h2 τ i, h1 τ i, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp]

end

theorem unitAt_det_co : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk x ≫ s₀ TF.Y Z = spMap φ → ∃ U : (X₀ TF.Y Z).Opens, x ∈ U ∧ ∀ y ∈ U, ∀ (φ' : c.F →+* (X₀ TF.Y Z).presheaf.stalk y) (f' : GlobalTheory.ShFam.EigFrame TF.Y φ' ((X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι)) (φK : c.F →+* (X₀ TF.Y Z).functionField) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φK ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk y ≫ s₀ TF.Y Z = spMap φ' → (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ s₀ TF.Y Z = spMap φK → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f' embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK' → ∀ τ, UnitAt y (fK'.co fK τ).det := by
  intro E _ _ _ H Dw l Xo c TF Z _ x φ f hφ
  haveI : IsIso (genι TF.Y) := GlobalTheory.VarFlag.isIso_genι
  let e : X₀ TF.Y Z ⟶ gen TF.Y := (barComp TF.Y Z).ι ≫ inv (genι TF.Y)
  have he : e ≫ genι TF.Y = (barComp TF.Y Z).ι := by simp [e]
  have hstrY : genStr TF.Y = genι TF.Y ≫ TF.Y.s := by
    have h0 : genι TF.Y ≫ TF.Y.s = genStr TF.Y ≫ spMap (RingHom.id c.F) := pullback.condition
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    rw [h1, Category.comp_id] at h0
    exact h0.symm
  obtain ⟨U, hU, φU, F, hxU, hUstr, -⟩ :=
    GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y (e x)
  let ψ : ∀ p : X₀ TF.Y Z, e p ∈ U → (Γ(gen TF.Y, U) →+* (X₀ TF.Y Z).presheaf.stalk p) := fun p hp =>
    (e.stalkMap p).hom.comp ((gen TF.Y).presheaf.germ U (e p) hp).hom
  have hψ : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ e = spMap (ψ p hp) ≫ hU.fromSpec := by
    intro p hp
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hU.fromSpecStalk_eq_fromSpecStalk hp, IsAffineOpen.fromSpecStalk,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  have hmono : ∀ {R : Type} [CommRing R] (a b : Γ(gen TF.Y, U) →+* R),
      spMap a ≫ hU.fromSpec = spMap b ≫ hU.fromSpec → a = b := fun a b h =>
    GlobalTheory.ShFam.EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 h)
  have hring : ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X₀ TF.Y Z) (ρ : c.F →+* R) (a : Γ(gen TF.Y, U) →+* R),
      q ≫ s₀ TF.Y Z = spMap ρ → q ≫ e = spMap a ≫ hU.fromSpec → ρ = a.comp φU := by
    intro R _ q ρ a h1 h2
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← h1, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hUstr, ← Category.assoc (spMap a), ← h2, hstrY]
    simp only [Category.assoc]
    rw [← Category.assoc e, he]
  have hpt : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ (barComp TF.Y Z).ι = spMap (ψ p hp) ≫ hU.fromSpec ≫ genι TF.Y := by
    intro p hp
    rw [← he, ← Category.assoc, hψ p hp, Category.assoc]
  have hgen : ∀ p : X₀ TF.Y Z, (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk p :=
    fun p =>
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec (X₀ TF.Y Z)).specializes (Set.mem_univ p))).symm
  obtain ⟨Fx, hFx⟩ := F.exists_isMap (ψ x hxU) (hring _ φ _ hφ (hψ x hxU)) (hpt x hxU)
  have hWx : ∀ τ, UnitAt x (algebraMap _ (X₀ TF.Y Z).functionField (Fx.co f τ).det) :=
    fun τ => ⟨_, EigFrame.isUnit_det_co Fx f τ, rfl⟩
  choose W hxW hW using fun τ => (hWx τ).exists_nhds
  refine ⟨⟨(e ⁻¹ᵁ U : Set (X₀ TF.Y Z)) ∩ ⋂ τ, (W τ : Set (X₀ TF.Y Z)),
    (e ⁻¹ᵁ U).isOpen.inter (isOpen_iInter_of_finite fun τ => (W τ).isOpen)⟩,
    ⟨hxU, Set.mem_iInter.2 hxW⟩, ?_⟩
  rintro y ⟨hyU, hyW⟩ φ' f' φK fK fK' hφ' hφK hfK hfK' τ
  rw [Set.mem_iInter] at hyW
  have hyU' : e y ∈ U := hyU
  obtain ⟨Fy, hFy⟩ := F.exists_isMap (ψ y hyU') (hring _ φ' _ hφ' (hψ y hyU')) (hpt y hyU')
  have hKp : ∀ p hp, spMap ((algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField).comp (ψ p hp)) ≫
      hU.fromSpec = (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ e := by
    intro p hp
    rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField)
      (ψ p hp), Category.assoc, ← hψ, ← Category.assoc, ← hgen]
  have hK : (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU') =
      (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField).comp (ψ x hxU) :=
    hmono _ _ ((hKp y hyU').trans (hKp x hxU).symm)
  have hKpt := (hKp y hyU').symm
  obtain ⟨FK, hFK⟩ := F.exists_isMap
    ((algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU'))
    (x' := (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)
    (hring _ φK _ hφK hKpt) (by rw [← he]; exact (reassoc_of% hKpt) (genι TF.Y))
  have hFyK : Fy.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFy hFK
  have hFxK : Fx.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFx (by rw [← hK]; exact hFK)
  have hy : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι := by
    rw [hgen y, Category.assoc]
  have hx : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι := by
    rw [hgen x, Category.assoc]
  have e1 := EigFrame.IsMap.co (τ := τ) hfK' hFyK hy
  have e2 := EigFrame.IsMap.co (τ := τ) hFxK hfK hx
  have dmap : ∀ {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R),
      (M.map g).det = g M.det := fun g _ M => (RingHom.map_det g M).symm
  rw [← EigFrame.co_mul fK' FK fK τ, Matrix.det_mul, e1, dmap]
  refine UnitAt.mul ⟨_, EigFrame.isUnit_det_co f' Fy τ, rfl⟩ ?_
  convert hW τ y (hyW τ) using 1
  erw [e2]
  exact dmap _ _

end GlobalTheory.FrameSpread
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameCoordinatesLocallyConstantUpToUnitsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep


theorem _root_.GlobalTheory.T.eigenFrameCoordinates_locallyConstant_upToUnits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk x ≫ s₀ TF.Y Z = spMap φ → ∃ U : (X₀ TF.Y Z).Opens, x ∈ U ∧ ∀ y ∈ U, ∀ (φ' : c.F →+* (X₀ TF.Y Z).presheaf.stalk y) (f' : GlobalTheory.ShFam.EigFrame TF.Y φ' ((X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι)) (φK : c.F →+* (X₀ TF.Y Z).functionField) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φK ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk y ≫ s₀ TF.Y Z = spMap φ' → (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ s₀ TF.Y Z = spMap φK → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f' embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK' → ∀ τ, UnitAt y (fK'.co fK τ).det := by
  first | exact @GlobalTheory.FrameSpread.unitAt_det_co | exact GlobalTheory.FrameSpread.unitAt_det_co | (intros; apply GlobalTheory.FrameSpread.unitAt_det_co <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidal

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigDiv

theorem exists_eigFrame_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (R : Type) [CommRing R] [IsLocalRing R] (p : Sp R ⟶ X₀ TF.Y Z), ∃ (φ : c.F →+* R) (_ : GlobalTheory.ShFam.EigFrame TF.Y φ (p ≫ (barComp TF.Y Z).ι)), p ≫ s₀ TF.Y Z = spMap φ := by
  intro E _ _ _ H Dw l Xo c TF Z R _ _ p
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [hid]; infer_instance
  haveI : IsIso (GlobalTheory.Toroidal.genι TF.Y) := inferInstanceAs (IsIso (pullback.fst TF.Y.s (spMap (RingHom.id c.F))))
  have hs : inv (GlobalTheory.Toroidal.genι TF.Y) ≫ GlobalTheory.Toroidal.genStr TF.Y = TF.Y.s := by
    rw [IsIso.inv_comp_eq]
    calc GlobalTheory.Toroidal.genStr TF.Y = GlobalTheory.Toroidal.genStr TF.Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = GlobalTheory.Toroidal.genι TF.Y ≫ TF.Y.s := pullback.condition.symm
  let x : Sp R ⟶ GlobalTheory.Toroidal.gen TF.Y := (p ≫ (barComp TF.Y Z).ι) ≫ inv (GlobalTheory.Toroidal.genι TF.Y)
  let φ : c.F →+* R := (Spec.preimage (p ≫ s₀ TF.Y Z)).hom
  have hφ : spMap φ = p ≫ s₀ TF.Y Z := Spec.map_preimage _
  have hx : x ≫ GlobalTheory.Toroidal.genStr TF.Y = spMap φ := by
    rw [hφ, Category.assoc, hs, Category.assoc]
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y R φ x hx
  have e : x ≫ GlobalTheory.Toroidal.genι TF.Y = p ≫ (barComp TF.Y Z).ι := by
    simp only [x, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨φ, e ▸ f, hφ.symm⟩

theorem ratio_mem {K : Type} [Field K] (S : Subgroup Kˣ) {ι : Type} [Fintype ι] (u v w : ι → Kˣ)
    (h : ∀ τ, (v τ : K) = w τ * u τ) (hw : ∀ τ, w τ ∈ S) (a : ι → ℤ) :
    (∏ τ, u τ ^ (-a τ)) / (∏ τ, v τ ^ (-a τ)) ∈ S := by
  have hv : ∀ τ, v τ = w τ * u τ := fun τ => Units.ext (by rw [Units.val_mul]; exact h τ)
  rw [← Finset.prod_div_distrib]
  refine S.prod_mem fun τ _ => ?_
  have e : u τ / v τ = (w τ)⁻¹ := by rw [hv, div_mul_eq_div_div_swap, div_self', one_div]
  rw [← div_zpow, e]
  exact S.zpow_mem (S.inv_mem (hw τ)) _

theorem exists_div {X : Scheme.{0}} [IsIntegral X] (g : X → X.functionFieldˣ)
    (h : ∀ x, ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, UnitAt y ((g x : X.functionField) / g y)) :
    ∃ D : CartierDiv X, ∀ x, D.IsEqn x (g x) :=
  ⟨show cartierGroup X from ⟨fun x => germOf x (g x), fun x => by
    obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, hx, g x, fun y hy => germOf_eq_iff.2 (hU y hy)⟩⟩, fun _ => rfl⟩

theorem exists_detDiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)], ∃ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ ∧ ∀ a : (E →+* ℂ) → ℤ, ∃ D : CartierDiv (X₀ TF.Y Z), CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) ∧ ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-a τ)) := by
  intro E _ _ _ H Dw l Xo c TF Z _
  have hloc : ∀ x : X₀ TF.Y Z, IsLocalRing ((X₀ TF.Y Z).presheaf.stalk x) := fun x => inferInstance
  obtain ⟨φ₀, f₀, h₀⟩ := @exists_eigFrame_stalk E _ _ _ H Dw l Xo c TF Z ((X₀ TF.Y Z).presheaf.stalk (genericPoint (X₀ TF.Y Z))) _ (hloc _) ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)))
  refine ⟨φ₀, f₀, h₀, fun a => ?_⟩
  choose φx fx hx using fun x : X₀ TF.Y Z => @exists_eigFrame_stalk E _ _ _ H Dw l Xo c TF Z ((X₀ TF.Y Z).presheaf.stalk x) _ (hloc x) ((X₀ TF.Y Z).fromSpecStalk x)
  have hpt : ∀ x : X₀ TF.Y Z, spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) ≫
      (X₀ TF.Y Z).fromSpecStalk x = (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) := fun x =>
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  have hφ : ∀ x, φ₀ = (algebraMap _ (X₀ TF.Y Z).functionField).comp (φx x) := fun x =>
    GlobalTheory.ShFam.EigLoc.spMap_inj (by rw [← h₀, ← hpt x, Category.assoc, hx x]; exact (Spec.map_comp _ _).symm)
  have hFK : ∀ x : X₀ TF.Y Z, ∃ fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀
      ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι),
      (fx x).IsMap (algebraMap _ (X₀ TF.Y Z).functionField) fK := fun x =>
    (fx x).exists_isMap (algebraMap _ (X₀ TF.Y Z).functionField) (hφ x)
      (by rw [← hpt x]; exact Category.assoc _ _ _)
  let fK := fun x => Classical.choose (hFK x)
  have hfK := fun x => Classical.choose_spec (hFK x)
  let g : ∀ fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι),
    (X₀ TF.Y Z).functionFieldˣ := fun fK => ∏ τ, (fK.isUnit_det_co f₀ τ).unit ^ (-a τ)
  have key : ∀ (y : X₀ TF.Y Z) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φ₀
      ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)),
      (∀ τ, UnitAt y (fK'.co fK τ).det) → UnitAt y ((g fK : (X₀ TF.Y Z).functionField) / g fK') := by
    intro y fK fK' hu
    have := ratio_mem (unitsAt y) (fun τ => (fK.isUnit_det_co f₀ τ).unit) (fun τ => (fK'.isUnit_det_co f₀ τ).unit)
      (fun τ => (fK'.isUnit_det_co fK τ).unit) (fun τ => by
        simp only [IsUnit.unit_spec]
        rw [← Matrix.det_mul, GlobalTheory.ShFam.EigFrame.co_mul]) (fun τ => hu τ) a
    rw [← Units.val_div_eq_div_val (g fK) (g fK')]
    exact this
  obtain ⟨D, hD⟩ := exists_div (fun x => g (fK x)) fun x => by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.T.eigenFrameCoordinates_locallyConstant_upToUnits E H Dw l Xo c TF Z x (φx x) (fx x) (hx x)
    exact ⟨U, hxU, fun y hy => key y _ _ (hU y hy (φx y) (fx y) φ₀ (fK x) (fK y) (hx y) h₀ (hfK x) (hfK y))⟩
  refine ⟨D, ?_, fun x => ⟨φx x, fx x, fun τ => (fK x |>.co f₀ τ).transpose,
    fun τ => (fK x |>.isUnit_det_co f₀ τ).unit, hx x, fun τ => (IsUnit.unit_spec _).trans (Matrix.det_transpose _).symm, fun τ i => ?_, hD x⟩⟩
  · refine GlobalTheory.T.flagSpacePullback_eigenDeterminantDivisor_eq_gradedLines E H Dw l Xo c TF Z φ₀ f₀ a D h₀ fun x φ f fK' hs hm => ?_
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.T.eigenFrameCoordinates_locallyConstant_upToUnits E H Dw l Xo c TF Z x φ f hs
    exact (hD x).iff_unitAt.2 (key x _ _ (hU x hxU (φx x) (fx x) φ₀ fK' (fK x) (hx x) h₀ hm (hfK x)))
  · have e : (fK x).v τ = fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x)
        (X₀ TF.Y Z).functionField)) ≫ (fx x).v τ k := funext (hfK x τ)
    rw [← e]
    exact (fK x).co_spec f₀ τ i

end GlobalTheory.EigDiv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_cartierDivisor_det_lieEigenparts_toroidal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)], ∃ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ ∧ ∀ a : (E →+* ℂ) → ℤ, ∃ D : CartierDiv (X₀ TF.Y Z), CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) ∧ ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-a τ)) := by
  first | exact @GlobalTheory.EigDiv.exists_detDiv | exact GlobalTheory.EigDiv.exists_detDiv | (intros; apply GlobalTheory.EigDiv.exists_detDiv <;> assumption)
end
end
