module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadingVectorFixedByClassStabiliserCharacterStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_coefficientVector_reading_realRepresentation_form : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {S : (I.rec7 l Z).what₂.Tau → SPar} (MX : DSModel (I.rec7 l Z).sp.X' S) (j : SmT MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)), GlobalTheory.Core.Rk.Top.IsJ u MX j → ∀ ℓ : SmT MX →ₗ[ℂ] ℂ, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v, ℓ v = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
  first | exact @GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ | exact GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ | (intros; apply GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormPrescribedValuesClassRepresentative

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PerIn

theorem exists_Mt_of_rep_values : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Formalism.BasicNotions.Ranks} {I : GlobalTheory.Mem.Col2.ChainIn E K ι R} (Q : GlobalTheory.Mem.Col2.PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ), (∀ b, Q.H b = ⊤) → ∀ (w : Q.S'.Cl → Formalism.L2.DIV.Pol ℂ ι (R.N R.m - 1)), (∀ c, w c ∈ Formalism.L2.DIV.VV ℂ Q.sgT) → (∀ c (s : Q.S'.Stab c), w c = (σ (Q.S'.chr c.1 s.1 : K))⁻¹ • Formalism.L2.DIV.rhoP Q.sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam c.1 s.1)) (w c)) → ∃ F : Q.Mt emb σ, ∀ c, F.1 c.1 (Q.S'.rep c) = w c := by
  intro E K ι _ _ _ _ _ _ _ R I Q emb σ _hH w hw hinv
  classical
  let φ : ∀ b, Q.S'.G b → Pol ℂ ι (R.N R.m - 1) → Pol ℂ ι (R.N R.m - 1) := fun b g x =>
    (σ (Q.S'.chr b g : K))⁻¹ • rhoP Q.sgT (embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam b g)) x
  have φmul : ∀ b (g h : Q.S'.G b) x, φ b (g * h) x = φ b g (φ b h x) := by
    intro b g h x
    simp only [φ, map_mul, Units.val_mul, mul_inv, Module.End.mul_apply, map_smul, smul_smul]
  have hinv' : ∀ c (s : Q.S'.G c.1), s • Q.S'.rep c = Q.S'.rep c → w c = φ c.1 s (w c) :=
    fun c s hs => hinv c ⟨s, hs⟩
  let F : ∀ b, Q.S'.D b → Pol ℂ ι (R.N R.m - 1) := fun b d => φ b (Q.S'.mv b d) (w (Q.S'.cl b d))
  have hcl : ∀ b (g : Q.S'.G b) (d : Q.S'.D b), Q.S'.cl b (g • d) = Q.S'.cl b d := fun b g d =>
    Sigma.ext rfl (heq_of_eq (Quotient.sound (MulAction.mem_orbit d g)))
  have hlaw : ∀ b (g : Q.S'.G b) d, F b (g • d) = φ b g (F b d) := by
    intro b g d
    set c := Q.S'.cl b d with hc
    have hrep : Q.S'.rep (Q.S'.cl b (g • d)) = Q.S'.rep c :=
      congrArg (Q.S'.rp b) (Quotient.sound (MulAction.mem_orbit d g))
    have h1 : Q.S'.mv b (g • d) • Q.S'.rep c = g • d := by
      convert Q.S'.mv_smul b (g • d) using 2; exact hrep.symm
    have h2 := Q.S'.mv_smul b d
    have hs : ((g * Q.S'.mv b d)⁻¹ * Q.S'.mv b (g • d)) • Q.S'.rep c = Q.S'.rep c := by
      rw [mul_smul, h1, _root_.mul_inv_rev, mul_smul, inv_smul_smul, inv_smul_eq_iff, h2]
    have hw := hinv' c _ hs
    show φ b (Q.S'.mv b (g • d)) (w (Q.S'.cl b (g • d))) = φ b g (φ b (Q.S'.mv b d) (w c))
    rw [hcl, ← φmul]
    conv_rhs => rw [hw, ← φmul, mul_inv_cancel_left]
  refine ⟨⟨F, fun b d => ⟨?_, fun g _ => hlaw b g d⟩⟩, ?_⟩
  · exact Submodule.smul_mem _ _ (polyAction_mem_VV _ _ (hw _))
  · rintro ⟨b, q⟩
    have hq : Q.S'.cl b (Q.S'.rep ⟨b, q⟩) = ⟨b, q⟩ := Sigma.ext rfl (heq_of_eq (Q.S'.rp_spec b q))
    have hr : Q.S'.rep (Q.S'.cl b (Q.S'.rep ⟨b, q⟩)) = Q.S'.rep ⟨b, q⟩ := congrArg (Q.S'.rp b) (Q.S'.rp_spec b q)
    have h1 : Q.S'.mv b (Q.S'.rep ⟨b, q⟩) • Q.S'.rep ⟨b, q⟩ = Q.S'.rep ⟨b, q⟩ := by
      convert Q.S'.mv_smul b (Q.S'.rep ⟨b, q⟩) using 2; exact hr.symm
    show φ b (Q.S'.mv b (Q.S'.rep ⟨b, q⟩)) (w (Q.S'.cl b (Q.S'.rep ⟨b, q⟩))) = w ⟨b, q⟩
    rw [hq]
    exact (hinv' ⟨b, q⟩ _ h1).symm

end GlobalTheory.Mem.Col2.PerIn
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormPrescribedValuesClassRepresentativeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rowForm_prescribed_values_class_representatives : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Formalism.BasicNotions.Ranks} {I : GlobalTheory.Mem.Col2.ChainIn E K ι R} (Q : GlobalTheory.Mem.Col2.PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ), (∀ b, Q.H b = ⊤) → ∀ (w : Q.S'.Cl → Formalism.L2.DIV.Pol ℂ ι (R.N R.m - 1)), (∀ c, w c ∈ Formalism.L2.DIV.VV ℂ Q.sgT) → (∀ c (s : Q.S'.Stab c), w c = (σ (Q.S'.chr c.1 s.1 : K))⁻¹ • Formalism.L2.DIV.rhoP Q.sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam c.1 s.1)) (w c)) → ∃ F : Q.Mt emb σ, ∀ c, F.1 c.1 (Q.S'.rep c) = w c := by
  first | exact @GlobalTheory.Mem.Col2.PerIn.exists_Mt_of_rep_values | exact GlobalTheory.Mem.Col2.PerIn.exists_Mt_of_rep_values | (intros; apply GlobalTheory.Mem.Col2.PerIn.exists_Mt_of_rep_values <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormReadingLevelFormLastSpace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.AdForm.exists_readsG_of_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ hX j hj P t a bad K eW hR heW hb hL f

  have hv : ∀ c : (I.stX a).Cl, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 →
      f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
    intro c
    obtain ⟨h₀, hh₀⟩ := GlobalTheory.Core.Rk.Top.Model.hasMat_exists (D := I.rec7 l Z) (K.y c)
    obtain ⟨w, hw, e⟩ := GlobalTheory.T.exists_coefficientVector_reading_realRepresentation_form I l Z u a R.MX j hj ((LinearMap.proj (h₀ * g.bT)).comp f.1)
    refine ⟨w, hw, fun v h hh => ?_⟩
    rw [GlobalTheory.Core.Rk.Top.Model.hasMat_pt hh hh₀]
    exact e v
  choose w hw hwv using hv
  obtain ⟨G', hG'⟩ := GlobalTheory.T.exists_rowForm_prescribed_values_class_representatives (I.perIn u a) B.fields.emb B.embLL (fun _ => rfl) w hw
    (fun c s => GlobalTheory.T.readingVector_fixed_by_class_stabiliser_character I hI hP l Z u R g c₀ hX j hj P t a bad K hR hb hL f c (w c) (hw c) (hwv c) s)
  refine ⟨G', fun c v h hh => ?_⟩
  rw [hwv c v h hh]
  have hz : ∀ c', eW.symm (Pi.single c (j v)) c' = (Pi.single c (j v) : (I.fm l u a).clsP → Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ) c' := by
    intro c'
    funext y'
    have := heW (eW.symm (Pi.single c (j v))) c' y' y' rfl
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  generalize eW.symm (Pi.single c (j v)) = z at hz
  have hzc : z c = j v := by rw [hz c, Pi.single_eq_same]
  have hzo : ∀ c', c' ≠ c → z c' = 0 := fun c' h => by
    rw [hz c']
    exact Pi.single_eq_of_ne h _
  haveI := (l.per u a).step.fin_stab c.1 ((I.perIn u a).S'.rep c)
  have hne : ((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI := (I.perIn u a).clFin (l.per u a)
  show _ = _ * (∑ c' : (I.perIn u a).S'.Cl, (I.perIn u a).wt c' • (Formalism.L2.DIV.pairB (K := ℂ) (I.perIn u a).sgT).compl₁₂
      (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT)
        (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) ∘ₗ LinearMap.proj c')
      (LinearMap.proj c' ∘ₗ (I.perIn u a).rd B.fields.emb B.embLL)) z G'
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  erw [Fintype.sum_eq_single c (fun c' hc' => by
    change (I.perIn u a).wt c' * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c')) _ = 0
    rw [hzo c' hc']
    simp only [map_zero, LinearMap.zero_apply, mul_zero])]
  change _ = _ * ((((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ)⁻¹) * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c)) (G'.1 c.1 ((I.perIn u a).S'.rep c)))
  rw [hzc, hG' c, ← mul_assoc]
  erw [mul_inv_cancel₀ hne, one_mul]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormReadingLevelFormLastSpaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  first | exact @GlobalTheory.AdForm.exists_readsG_of_level | exact GlobalTheory.AdForm.exists_readsG_of_level | (intros; apply GlobalTheory.AdForm.exists_readsG_of_level <;> assumption)
end
end
