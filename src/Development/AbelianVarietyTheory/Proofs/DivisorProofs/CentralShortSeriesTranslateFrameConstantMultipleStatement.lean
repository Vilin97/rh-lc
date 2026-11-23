module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovAtBaseRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LargeConstantLeParamCube
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatOfInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFifth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortAtFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortCentralMove
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFrameOfRichRec

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.BigOn.Inhab

namespace GlobalTheory.BigOn.CoreWit

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.JoinChr in
theorem exists_val_of_chrEq {c : (Formalism.L2.Theta.AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ)
    (x : (Formalism.L2.Theta.AE D)ˣ) : ∃ y, ((c x : Circle) : ℂ) = ((χ.1 y : ℂˣ) : ℂ) := by
  have hχ := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.2 c χ h
  obtain ⟨Θ, hc, hinc, hloc⟩ := GlobalTheory.CharTransport.exists_hom D
  let u : (Formalism.L2.Theta.AE D)ˣ →* Neutral.B1.Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (Formalism.L2.Theta.AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have h' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · refine (hcoe _).trans ?_
      have := congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ))
        (Units.ext (hinc x) : u (Units.map (Formalism.L2.Theta.incA D).toMonoidHom x) = Units.map (algebraMap D.host.E _).toMonoidHom x)
      exact this.trans (congrArg (fun y : ℂˣ => (y : ℂ)) (χ.2.2 x))
    · refine (hcoe _).trans (congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ)) (Units.ext ?_))
      change Θ (x : Formalism.L2.Theta.AE D) = _
      rw [hx, hloc P e he]
  exact ⟨u x, by rw [(GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 c c' χ h h', hcoe]⟩

end GlobalTheory.BigOn.CoreWit

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverValueRoot

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.OnCmp.CoverRoot

theorem xiVal_cast {D : D7} (T : Full D) (hT : LawsFull T) (j n : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : σ = T.toTop.toCore.σ₀) (W : HSp D) (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    ∃ (U₂ : _) (dict₂ : _), CXiVal W hr σ (Tup := Unit) (fun _ => T.dδ j n) U₂ dict₂
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (T.x₀ j σ) fun _ => T.xi := by
  subst hσ hV
  obtain ⟨_, U, d, h⟩ := hT.xiVal j hj n
  exact ⟨U, d, h⟩

theorem value_mem {D : D7} (T : Full D) (hT : LawsFull T) (j n : ℕ) (hj : InR D j) (τ : (T.dδ j n).c₂.F →+* ℂ)
    (hτ : τ = (T.dδ j n).c₂.F.val.toRingHom) (y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt τ)) :
    ∃ z, toC (evR (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).cδ y) = τ z := by
  subst hτ
  obtain ⟨Cls, _, _, δ, gdet, -, h⟩ := hT.sh.dRoot j hj n
  exact ⟨_, h y⟩


open GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal GlobalTheory.AdTh.CoverVal in

theorem cover_value_root : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ χ : (AE D)ˣ →* Circle, ChrEq χ (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) → ∃ c0' : ℂ, c0' ∈ D.what₂.embLL.range ∧ (∃ m : ℕ, 0 < m ∧ c0' ^ m = 1) ∧ (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hR i hO v _ hval0 hrun χ hχ
  have hI : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hs : (O i).s0 = T.toTop.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨U₂, dict₂, c0, hroot, hc⟩ := xiVal_cast T hT _ (Vc D i).rank (inR i) (O i).s0 hs (Wc D i) (O i).hV (rank_Wc i)
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc ()
  have hlev := hT.sh.dLev _ (inR i) (Vc D i).rank
  have hA := hT.lvA _ (inR i) (Vc D i).rank
  obtain ⟨-, -, -, χ₁, hχ₁, hxi⟩ := hrun
  obtain rfl : χ₁ = χ := GlobalTheory.ChrEqUnique.idc_unique D _ _ _ hχ₁ hχ
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hR hI i (O i).s0
    hs (T.dict _ (O i).s0 1).1
  have hτ : (O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F) =
      (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F.val.toRingHom := RingHom.ext fun _ => rfl
  have hσ : GoodEmb (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ((O i).s0.comp
      ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((U₂ ()).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((U₂ ()).X j) (T.x₀ ((i : ℕ) + 1) (O i).s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hex, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  have hv : ∀ (k : GA D (Wc D i)) (xk : (AE D)ˣ), IsDetRoot (Wc D i) k xk →
      rdU (U₂ ()) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ (dict₂ () k).1 (dict₂ () k).2 = c0 * ((χ₁ xk : Circle) : ℂ) := by
    intro k xk hxk
    obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
    obtain ⟨a, ha⟩ := hrat γ' hγ'
    have hv := hval k γ' ⟨hγ', h2, h3⟩
    rw [hxi _ _ (hmul _ _ _ _ ha hxk), map_mul, hχ.1.2 a, _root_.one_mul] at hv
    exact hv
  have hat := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (U₂ ()) hσ hU h1 hA R.θ (Wc D i) (rank_Wc i)
    (dict₂ ()) (iotaW T.J i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt
  refine ⟨c0, ?_, hroot, ?_⟩
  · obtain ⟨x1, hx1⟩ := hex 1
    obtain ⟨hon, -⟩ := hat 1
    obtain ⟨-, hu2, -⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E D.R.r ((U₂ ()).X (dict₂ () 1).1).p0
      ((U₂ ()).X (dict₂ () 1).1).Ψ ((U₂ ()).X (dict₂ () 1).1).Gm ((U₂ ()).X (dict₂ () 1).1).Gm_herm
    have hd : (dict₂ () 1).2 ∈ ((U₂ ()).X (dict₂ () 1).1).dom := (hu2 _ hon).1
    obtain ⟨z, hz⟩ := value_mem T hT _ _ (inR i) _ hτ ((U₂ ()).un _ ⟨_, hd⟩)
    have h2 : c0 * ((χ₁ x1 : Circle) : ℂ) = _ := ((hv 1 x1 hx1).symm.trans (dif_pos hd)).trans hz
    obtain ⟨y, hy⟩ := GlobalTheory.BigOn.CoreWit.exists_val_of_chrEq hχ x1
    obtain ⟨b, hb⟩ := hval0 y
    have hres := res_embLL T.J hI.alg hI.laws.pins.2.2.1
    refine ⟨algebraMap T.Q.c.F D.what₂.LL ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm z) / b, ?_⟩
    rw [map_div₀, hb, ← hy, div_eq_iff (Circle.coe_ne_zero _), h2]
    exact (DFunLike.congr_fun hres _).trans (DFunLike.congr_fun hs.symm _)
  · intro X g bas idx e k xk mk hX hp hsy hi hL hxk hmk hk y₂ A₂ hA₂
    obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := hat k
    obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (U₂ ())) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T.J i)
      _ Wt (dict₂ () k).1 (dict₂ () k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hsy hi hL hmk hk y₂ A₂ hA₂
    exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans (hv k xk hxk))

end GlobalTheory.OnCmp.CoverRoot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShortSeriesTranslateFrameConstantMultiple

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section
namespace GlobalTheory.HeartFrame

theorem splitOffBad_of_mul {D : D7} (V : HSp D) (a b : ℕ) (h : GA D V) (hs : SplitOffBad V (a * b) h) : SplitOffBad V a h := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := hs
  refine ⟨h1, e, P, h2, fun PP hPP ha => h3 PP hPP ?_, h4⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ ha



theorem central_short_series_frame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ z ∈ Subgroup.center G, ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) (actLev T.J.toCore.Q.c (O i).lev2 z⁻¹ ((F₀).1 : T.R ((i : ℕ) + 1))) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 z hz
  obtain ⟨x', ε, hx', hε, hmv⟩ := GlobalTheory.CentralLevelMove.short_central_move D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h (splitOffBad_of_mul _ _ _ _ hSB) hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 z hz
  obtain ⟨h0L, m0, hm0, h0⟩ := GlobalTheory.AdTh.CoverRoot.covAt_base_root D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP c0 hcov
  obtain ⟨c0', h1L, ⟨m1, hm1, h1⟩, hcT⟩ := GlobalTheory.OnCmp.CoverRoot.cover_value_root D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP v hF0 hdel hRun χ hK.chr
  have hrat : c0' * c0⁻¹ ∈ D.what₂.embLL.range := by
    obtain ⟨a, ha⟩ := h1L
    obtain ⟨b, hb⟩ := h0L
    exact ⟨a * b⁻¹, by rw [map_mul, map_inv₀, ha, hb]⟩
  have hroot : (c0' * c0⁻¹) ^ (m1 * m0) = 1 := by
    rw [mul_pow, inv_pow, pow_mul, h1, one_pow, mul_comm m1, pow_mul, h0]
    simp
  obtain ⟨y₀, c, hrk, hint, hmain⟩ := GlobalTheory.FrameShort.short_at_frame D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x' P y hUm hTb hTd hLev hx' hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 c0' hrat ⟨m1 * m0, Nat.mul_pos hm1 hm0, hroot⟩ hcT
  refine ⟨y₀, ε * c, hrk, fun lam hlam => ?_, fun φ' hφ' w hw F₀ hF₀ g => ?_⟩
  · obtain ⟨s, hs, hsi⟩ := hint lam hlam
    refine ⟨s, hs, ?_⟩
    rw [mul_left_comm]
    exact hε.mul hsi
  obtain ⟨F₁, hF₁, he⟩ := hmv F₀ hF₀
  have e3 := hmain φ' hφ' w hw F₁ hF₁ g
  rw [he, map_mul]
  linear_combination (D.what₂.embLL ε) * e3

end GlobalTheory.HeartFrame
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShortSeriesTranslateFrameConstantMultipleStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.centralShortSeriesTranslate_frameConstant_multiple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ z ∈ Subgroup.center G, ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) (actLev T.J.toCore.Q.c (O i).lev2 z⁻¹ ((F₀).1 : T.R ((i : ℕ) + 1))) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  first | exact @GlobalTheory.HeartFrame.central_short_series_frame | exact GlobalTheory.HeartFrame.central_short_series_frame | (intros; apply GlobalTheory.HeartFrame.central_short_series_frame <;> assumption)
end
end
