module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.HermitianForms.TiedTwP
public import Formalism.LocalToGlobal.HermitianForms.TiedTwPGen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleIntegralFormsRowPlaceByPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRhoStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowForms_weight_eq_parameter_sub_rho : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ τ (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)), (((I.fm l u a).sg τ).w i : ℚ) = Formalism.L2.Forms.sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  first | exact @GlobalTheory.Mem.Col2.TC.fm_sg_eq | exact GlobalTheory.Mem.Col2.TC.fm_sg_eq | (intros; apply GlobalTheory.Mem.Col2.TC.fm_sg_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularForms

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie




theorem ptC_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ z : (I.per l u a).Wrow, z ∈ (I.fm l u a).ptC ↔ GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z ∈ FiC K.lev (Formalism.L2.Forms.embT (I.rec7 l Z)) (sgTG (I.fm l u a)) K.y := by
  intro B X I hI hP l Z u a Q K hQ hQ' hR z
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u a).sgT = (sgTG (D := I.rec7 l Z) (I.fm l u a) : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
    funext τ
    obtain ⟨a, ha⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
      rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hc : ∀ c (s : (I.stX a).Stab c) (κ : K.lev.U), (K.y c).1 =
      bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 →
      ((K.lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
    intro c s κ e
    let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
    have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
    have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
    have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
        ((I.stX a).rep c).1.1 := by
      have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
        congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
      conv_rhs => rw [← e1]
      refine Eq.trans ?_ (smul_smul _ _ _).symm
      have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
          GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
          FrmG.incl _ _ s.1 := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact (inv_mul_cancel _).symm
        · exact (one_mul _).symm
        · exact (one_mul _).symm
      exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
    have hst := hR.stab c s
    let yc : GA B (B.R.N B.R.m - 1) := (K.y c).1
    let kk : GA B (B.R.N B.R.m - 1) := κ.1
    have e' : yc = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * yc * kk := by
      have h0 := e
      rw [show (K.stabI c s).1 = (I.stX a).gam c.1 s.1 from hst] at h0
      exact h0
    have hyk : yc * kk = ratAd B.host.F (s.1.1)⁻¹ * yc := by
      have e3 : ratAd B.host.F (s.1.1)⁻¹ =
          (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
        unfold ratAd
        rw [map_inv, map_inv]
        rfl
      rw [e3]
      conv_rhs => rw [e']
      group
    have hq : PtOf (yc * kk) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
      rw [hyk, hact]
      exact hp
    exact hR.chr c κ κ0 hgam hq
  letI : Algebra (I.rec7 l Z).host.F B.fields.E := (inferInstance : Algebra (I.rec7 l Z).host.F (I.rec7 l Z).host.E)
  exact mem_Fi_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT K.lev hemb hsg K.y K.y_bij K.stabI
    (fun c γ => K.stabI_range c γ) (fun c s => hR.stab c s) hc z

end GlobalTheory.Mem.Col2.TwP

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularFormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tupleChain_complexForms_eq_algebraicModularForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ z : (I.per l u a).Wrow, z ∈ (I.fm l u a).ptC ↔ GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z ∈ FiC K.lev (Formalism.L2.Forms.embT (I.rec7 l Z)) (sgTG (I.fm l u a)) K.y := by
  first | exact @GlobalTheory.Mem.Col2.TwP.ptC_tw | exact GlobalTheory.Mem.Col2.TwP.ptC_tw | (intros; apply GlobalTheory.Mem.Col2.TwP.ptC_tw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainFormsRationalIffFrameValues

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie

theorem ptEmb_iff_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ z : (I.per l u a).Wrow, (∃ x, (I.fm l u a).ptEmb x = z) ↔ z ∈ (I.fm l u a).ptC ∧ ∀ c, ∃ Pc ∈ RatSpan (I.rec7 l Z) (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) 1 Pc := by
  intro B X I hI hP l Z u a z
  have hsg : sgTG (D := I.rec7 l Z) (I.fm l u a) = (I.perIn u a).sgT := by
    funext τ
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (k + 1) := by
      rw [hk, show B.R.m * (2 * k + 1 + 1) = 2 * (B.R.m * (k + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = k + 1 := by omega
    show Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := congrArg shiftOf hsg
  exact rat_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT (l.fmL u a).famP (VV_shW B.wts.sgW _) hsh z

end GlobalTheory.Mem.Col2.TwP

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainFormsRationalIffFrameValuesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tupleChain_forms_rational_iff_frame_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ z : (I.per l u a).Wrow, (∃ x, (I.fm l u a).ptEmb x = z) ↔ z ∈ (I.fm l u a).ptC ∧ ∀ c, ∃ Pc ∈ RatSpan (I.rec7 l Z) (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) 1 Pc := by
  exact @GlobalTheory.Mem.Col2.TwP.ptEmb_iff_rat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsXTupleChainOfLevelReading

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section


theorem GlobalTheory.Mem.Col2.TwP.weightedInner_twisted : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ (o : Formalism.L2.Forms.FrP (I.rec7 l Z)), o.IsON → ∀ (z z' : (I.per l u a).Wrow) (Pc Qc : (I.fm l u a).clsP → MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) ℂ), (∀ c, Pc c ∈ CSpan (I.fm l u a).sg) → (∀ c, Qc c ∈ CSpan (I.fm l u a).sg) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c)) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z' c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c)) → (I.fm l u a).ipP z z' = ∑ c, ((Nat.card ((I.fm l u a).stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll (I.fm l u a).sg (Qc c) (Pc c) := by
  intro B X I hI hP l Z u a o ho z z' Pc Qc _ _ hz hz'
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hG : ∀ τ, gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) τ = 1 := fun τ => by
    rw [hgP, gramC_one]
  have hsh : shiftOf (sgTG (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  show (I.perIn u a).ipP B.fields.emb B.embLL (l.per u a) z z' = _
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : z c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz c
  have e2 : z' c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz' c
  show (I.perIn u a).wt c * ipVal B.fields.emb B.embLL (I.perIn u a).sgT (z c) (z' c) = _
  rw [e1, e2]
  exact congrArg₂ (· * ·) rfl (MetricTie.ipVal_step B.fields.emb B.embLL (I.perIn u a).sgT hl hsh hG id (fun _ => rfl) o ho (Pc c) (Qc c))


theorem GlobalTheory.Mem.Col2.TwP.norm_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (K : ClassesAtPrimes (I.fm l u a) bad) {okW : (I.rec7 l Z).what₂.places.Pl → Prop} (V : ValuationAtPrimes K okW), (∀ z, V.eW z = GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z) → NormPTieG V := by
  intro B X I hI hP l Z u a bad K okW V hV s x Pc hPc o ho
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  have h := @MetricTie.norm_step _ _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL (I.perIn u a).sgT (I.stX a) (base_fOk B)
    (l.per u a).step (l.fmL u a).famP ((I.perIn u a).clFin (l.per u a)) _ hl _ hsh _ _
    (fun τ => by rw [hgP, gramC_one]; rfl) (fun y => (y : Formalism.L2.Forms.FrP (I.rec7 l Z))) (fun _ => rfl) s x Pc
    (fun c z => by
      have e := (congrFun (hV ((I.fm l u a).ptEmb x)) c).symm.trans (hPc c)
      exact congrFun e z) o ho
  refine h.trans (Finset.sum_congr rfl fun c _ => ?_)
  congr 2
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  rfl



theorem GlobalTheory.Mem.Col2.TwP.forms_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∃ V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T), NormPTieG V ∧ ∀ z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → V.eW z c s = z c s' := by
  intro B X I hI hP l Z u a Q K hQ hQv hK
  let V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T) :=
    { sg := GlobalTheory.T.rowForms_weight_eq_parameter_sub_rho I hI hP l Z u a
      eW := GlobalTheory.Mem.Col2.TwP.eWt I l Z u a
      ptC := GlobalTheory.T.tupleChain_complexForms_eq_algebraicModularForms I hI hP l Z u a Q K hQ hQv hK
      ipP := GlobalTheory.Mem.Col2.TwP.weightedInner_twisted I hI hP l Z u a
      rat := GlobalTheory.T.tupleChain_forms_rational_iff_frame_values I hI hP l Z u a
      lat := GlobalTheory.T.tuple_integralForms_row_place_by_place I hI hP l Z u a Q K hQ hQv hK }
  refine ⟨V, GlobalTheory.Mem.Col2.TwP.norm_tw I hI hP l Z u a K V fun _ => rfl, fun z c s s' h => ?_⟩
  exact GlobalTheory.Mem.Col2.TwP.eWt_apply I l Z u a z c s s' h

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsXTupleChainOfLevelReadingStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.formsX_tupleChain_of_levelReading : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∃ V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T), NormPTieG V ∧ ∀ z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → V.eW z c s = z c s' := by
  first | exact @GlobalTheory.Mem.Col2.TwP.forms_tw | exact GlobalTheory.Mem.Col2.TwP.forms_tw | (intros; apply GlobalTheory.Mem.Col2.TwP.forms_tw <;> assumption)
end
end
