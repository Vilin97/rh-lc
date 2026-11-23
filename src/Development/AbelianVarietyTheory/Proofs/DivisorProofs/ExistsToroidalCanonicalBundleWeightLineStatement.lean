module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidalStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerDivisorToroidalComponent
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerDivisorToroidalComponentStatement

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

theorem _root_.GlobalTheory.T.exists_logKodairaSpencer_divisor_toroidalComponent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim) (D' : CartierDiv (X₀ TF.Y Z)) (r : K.bundle.ι → (X₀ TF.Y Z).functionFieldˣ), Presents D' K.bundle r → ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∀ D : CartierDiv (X₀ TF.Y Z), (∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)))) → ∃ h : (X₀ TF.Y Z).functionField, ∀ x : X₀ TF.Y Z, ∃ g g' : (X₀ TF.Y Z).functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧ RegAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ∧ (UnitAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  first | exact @GlobalTheory.LogKSDiv.exists_logKS_div | exact GlobalTheory.LogKSDiv.exists_logKS_div | (intros; apply GlobalTheory.LogKSDiv.exists_logKS_div <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecDivNonzeroLocusEq

section

@[expose] public section

set_option autoImplicit false

noncomputable section

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

namespace GlobalTheory.Cartier.RatSecDiv

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_mul_unit_iff {x : X} {a u : X.functionField} (hu : UnitAt x u) :
    UnitAt x (a * u) ↔ UnitAt x a := by
  refine ⟨fun h => ?_, fun h => h.mul hu⟩
  have e : a = a * u * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one]
  rw [e]; exact h.mul hu.inv

theorem local_of {D D' : CartierDiv X} {V : X.Opens} {h : X.functionField}
    (H : ∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V))
    {x : X} {gi rk : X.functionFieldˣ} (hi : D.IsEqn x gi) (hk : D'.IsEqn x rk) :
    RegAt x (h * (gi : X.functionField) / (rk : X.functionField)) ∧
      (UnitAt x (h * (gi : X.functionField) / (rk : X.functionField)) ↔ x ∈ V) := by
  obtain ⟨g, g', hg, hg', hr, hu⟩ := H x
  have u : UnitAt x (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) :=
    (hg.iff_unitAt.1 hi).mul (hk.iff_unitAt.1 hg')
  have e : h * (gi : X.functionField) / (rk : X.functionField) =
      h * (g : X.functionField) / (g' : X.functionField) *
        (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) := by
    have := g.ne_zero; have := g'.ne_zero; have := rk.ne_zero
    field_simp
  rw [e, unitAt_mul_unit_iff u]
  exact ⟨hr.mul u.regAt, hu⟩

end GlobalTheory.Cartier.RatSecDiv


open GlobalTheory.Cartier.RatSecDiv in
theorem GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq :
    ∀ {X : Scheme.{0}} [IsIntegral X] (D D' : CartierDiv X) (L : LB X) (r : L.ι → X.functionFieldˣ),
    Presents D' L r → ∀ (V : X.Opens) (h : X.functionField),
    (∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V)) →
    ∃ θ : (LB.div (toLB D) L).Sec, nonzeroLocus θ = V := by
  intro X _ D D' L r hP V h H
  have key (p : (LB.div (toLB D) L).ι) : ∃ a : Γ(X, (LB.div (toLB D) L).U p), ∀ hp,
      fnOf _ hp a = h * (p.1.1.2 : X.functionField) / (r p.2 : X.functionField) := by
    by_cases hp : genericPoint X ∈ (LB.div (toLB D) L).U p
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hp fun x hx =>
        (local_of H (p.1.2.2 x hx.1) (hP.isEqn p.2 x hx.2)).1
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (hp h').elim⟩
  choose a ha using key
  refine ⟨⟨a, fun p q => fn_ext fun hpq => ?_⟩, ?_⟩
  · have hp : genericPoint X ∈ (LB.div (toLB D) L).U p := hpq.1
    have hq : genericPoint X ∈ (LB.div (toLB D) L).U q := hpq.2
    refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg _ (fnOf_resG _ hpq _))).symm)
    rw [ha p hp, ha q hq]
    have eL := hP.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2)
    have e1 : fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val =
        (p.1.1.2 : X.functionField) / (q.1.1.2 : X.functionField) := fnOf_toLB_g _ _ _
    have eg : fnOf _ hpq ((LB.div (toLB D) L).g p q).val =
        fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val *
          (fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val)⁻¹ := by
      change fnOf _ hpq ((res _ ((toLB D).g p.1 q.1) * (res _ (L.g p.2 q.2))⁻¹ : Γ(X, _)ˣ).val) = _
      erw [Units.val_mul, map_mul, map_units_inv]
      exact congrArg₂ (· * ·) (fnOf_resG _ _ _) (congrArg _ (fnOf_resG _ _ _))
    have eL' : fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val =
        (r p.2 : X.functionField) / (r q.2 : X.functionField) :=
      (eq_div_of_mul_eq (r q.2).ne_zero eL.symm)
    rw [eg, e1, eL']
    have := (p.1.1.2).ne_zero; have := (q.1.1.2).ne_zero
    have := (r p.2).ne_zero; have := (r q.2).ne_zero
    field_simp
  · have hmem (p : (LB.div (toLB D) L).ι) (y : X) (hy : y ∈ (LB.div (toLB D) L).U p) :
        y ∈ X.basicOpen (a p) ↔ y ∈ V := by
      rw [← unitAt_fnOf_iff hy (gen_mem hy), ha p (gen_mem hy)]
      exact (local_of H (p.1.2.2 y hy.1) (hP.isEqn p.2 y hy.2)).2
    refine le_antisymm (iSup_le fun p y hy => (hmem p y (X.basicOpen_le _ hy)).1 hy) fun y hy => ?_
    obtain ⟨i, hi⟩ := exists_chart (isLB_toLB D) y
    obtain ⟨k, hk⟩ := exists_chart hP.isLB y
    exact Opens.mem_iSup.2 ⟨(i, k), (hmem (i, k) y ⟨hi, hk⟩).2 hy⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToroidalCanonicalBundleWeightLine

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
namespace GlobalTheory.LogCanon

theorem exOf_kapBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) :
    (fun ix : Ix Dw => Option.elim ix 0 fun x =>
      (fun τ : E →+* ℂ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) x.1) =
      AllWt.exOf Dw (kapBase Dw) 0 := by
  funext ix
  rcases ix with _ | ⟨τ, i⟩
  · rfl
  · by_cases h' : τ (H.rt : E) = H.rt0
    · have hi : (i : ℕ) < Dw.p := by
        have := i.2; simp only [Datum.mult, if_pos h'] at this; exact this
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_pos h', dif_pos h', dif_pos hi, kapBase, sub_zero,
        if_pos hi]
    · have hi : (i : ℕ) < Dw.q := by
        have := i.2; simp only [Datum.mult, if_neg h'] at this; exact this
      have hc : conjEmb τ (H.rt : E) = H.rt0 := by
        have := (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H τ).resolve_left h'
        unfold InPsi at this
        rw [ComplexEmbedding.conjugate_coe_eq] at this
        exact this
      have hn : ¬ (Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p) := by omega
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_neg h', dif_neg h', dif_pos hc, dif_pos hi, kapBase,
        if_neg hn, neg_neg, sub_zero]

theorem exists_kap_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim), ∃ (κ : LB (X₀ TF.Y Z)) (hκ : κ.IsLB), CechPic.pull (π₀ TF.X Z) (cls κ hκ) = cls (L₀ TF.X Z (kapBase Dw)) (isLB_L₀ TF.X Z _) ∧ ∃ θ : (LB.div κ K.bundle).Sec, nonzeroLocus θ = (j₀ TF.Y Z).opensRange := by
  intro E hE hNumber hCM H Dw l Xo c TF Z hpq hF hSmooth K
  obtain ⟨hI, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  letI : IsIntegral (X₀ TF.Y Z) := hI
  obtain ⟨φ₀, f₀, hgen, hdiv⟩ := GlobalTheory.T.exists_cartierDivisor_det_lieEigenparts_toroidal E H Dw l Xo c TF Z
  obtain ⟨D, hpull, hD⟩ := hdiv fun τ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p
  refine ⟨toLB D, isLB_toLB D, ?_, ?_⟩
  · rw [exOf_kapBase Dw] at hpull
    exact hpull
  · obtain ⟨i₀, hi₀⟩ := exists_chart K.isLB (genericPoint (X₀ TF.Y Z))
    have hP := presents_ofLB K.isLB i₀ hi₀
    have hKS := @GlobalTheory.T.exists_logKodairaSpencer_divisor_toroidalComponent
      E hE hNumber hCM H Dw l Xo c TF Z hpq hF hI hSmooth K
      (ofLB K.isLB i₀ hi₀) (frameRat K.bundle i₀ hi₀) hP φ₀ f₀ hgen D hD
    obtain ⟨h, hh⟩ := hKS
    exact GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq D _ K.bundle _ hP _ h hh
end GlobalTheory.LogCanon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToroidalCanonicalBundleWeightLineStatement

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

theorem _root_.GlobalTheory.T.exists_toroidalCanonicalBundle_weight_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim), ∃ (κ : LB (X₀ TF.Y Z)) (hκ : κ.IsLB), CechPic.pull (π₀ TF.X Z) (cls κ hκ) = cls (L₀ TF.X Z (kapBase Dw)) (isLB_L₀ TF.X Z _) ∧ ∃ θ : (LB.div κ K.bundle).Sec, nonzeroLocus θ = (j₀ TF.Y Z).opensRange := by
  first | exact @GlobalTheory.LogCanon.exists_kap_theta | exact GlobalTheory.LogCanon.exists_kap_theta | (intros; apply GlobalTheory.LogCanon.exists_kap_theta <;> assumption)
end
end
