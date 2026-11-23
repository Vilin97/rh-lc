module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinationsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrime
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiLevEqConstMulLocFacStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_chain_descent_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 1 ≤ B.R.m → IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.g.vac j) ∧ IsLatVac (heisO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _) (stdHom _ _) (a.g.vac j) ∧ IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  first | exact @_root_.GlobalTheory.Fam.VacTheta.main_alt_alt | exact _root_.GlobalTheory.Fam.VacTheta.main_alt_alt | (intros; apply _root_.GlobalTheory.Fam.VacTheta.main_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrimeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime : GlobalTheory.AdForm.TwVec' := by
  first | exact @GlobalTheory.AdForm.twVec' | exact GlobalTheory.AdForm.twVec' | (intros; apply GlobalTheory.AdForm.twVec' <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumDTLevelPrime

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem ratDatum_dT_levelPrime_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch₀ j) (γ : J.Ch₀ (j + 1)), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ eT (fun z => B.embLL (Formalism.L2.Col.phiT B.fields.K (J.A.p0 j α).1.1.deco.1 (J.A.p0 (j + 1) γ).1.1.deco.1 (GlobalTheory.QTw.homOf I l Z j hj z))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha hTr t J hJ eT heT j hj α γ
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  have hS := ha.shape
  have hP : (fun v => v ∈ a.v.tP) = (fun v => ∃ i, v = (a.o.p i).v) := funext fun x => propext (hS.pre.tP x)
  have hPl : GlobalTheory.FinPl.Places a.o.p a.o.I (fun v => ∃ i, v = (a.o.p i).v) :=
    ⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, fun _ => Iff.rfl, fun i => (hS.pre.char i).2⟩
  have hR : GlobalTheory.FinPl.Reps (_root_.GlobalTheory.Fam.pk_z W).ψ (a.o.β j) (a.o.β (j + 1)) (a.g.x j).L (a.g.x (j + 1)).L
      (fun i => GlobalTheory.LatPair.phiOne (a.o.Q j i) (a.o.Q (j + 1) i)) a.o.I (fun v => ∃ i, v = (a.o.p i).v) (a.v.dT j) := by
    rw [← hP]; exact ⟨(ha.vis.atT j).1, hS.rep j hj⟩
  exact GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime I hAll.tr.ok hAll.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is _ _ _ _ _ hTr.pinX a.k a.ι a.o.p a.o.β a.o.Q
    hTr.std a.o.I hPl j hj α γ (a.v.dT j) hR eT heT
end GlobalTheory.Fam
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumDTLevelPrimeStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_twist_reduction_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch₀ j) (γ : J.Ch₀ (j + 1)), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ eT (fun z => B.embLL (Formalism.L2.Col.phiT B.fields.K (J.A.p0 j α).1.1.deco.1 (J.A.p0 (j + 1) γ).1.1.deco.1 (GlobalTheory.QTw.homOf I l Z j hj z))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  first | exact @_root_.GlobalTheory.Fam.ratDatum_dT_levelPrime_alt | exact _root_.GlobalTheory.Fam.ratDatum_dT_levelPrime_alt | (intros; apply _root_.GlobalTheory.Fam.ratDatum_dT_levelPrime_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VTDisjointVGs

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.DisjProof
theorem vT_disjoint_vGs_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  exact Finset.disjoint_left.2 fun P h1 h2 =>
    Formalism.L2.Col.piT_notMem_vGs hPr u ⟨P, h2⟩ ((Formalism.L2.Col.mem_divs hT0 P).1 h1)
end GlobalTheory.Mem.Col2.DisjProof
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VTDisjointVGsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.type_primes_disjoint' : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  first | exact @_root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt | exact _root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt | (intros; apply _root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumXiOffCommon

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam
theorem ratDatum_xiOff_common_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ e, IsIdemSum e ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ, IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ e (fun z => C j * xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha haT hiA
  obtain ⟨C, hC, hloc⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_symmetry_alt W hAll u a ha haT hiA
  refine ⟨fun j => (C j)⁻¹, fun j hj => inv_ne_zero (hC j hj), ?_⟩
  intro t J hJ e he j hj α γ
  obtain ⟨Ξl, hΞl, hfac⟩ := hloc t J hJ j hj α γ
  obtain ⟨hv0, hvl, hvT⟩ := _root_.GlobalTheory.T.true_geometry_chain_descent_alt W hAll u a ha haT j hj
  have hinj : Function.Injective fun n : Fin a.n => ((a.pl n : (_root_.GlobalTheory.Fam.pk_z W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) :=
    fun n n' h => a.pl.injective (Subtype.ext h)
  have hmem : ∀ PP, PP ∈ (B.primes X).vGs ↔ ∃ n : Fin a.n, ((a.pl n : (_root_.GlobalTheory.Fam.pk_z W).Pg) : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) = PP := by
    intro PP
    refine Iff.trans (hAll.lev.2.1 PP).symm ⟨fun h => ⟨a.pl.symm ⟨PP, h⟩, by rw [Equiv.apply_symm_apply]⟩, ?_⟩
    rintro ⟨n, rfl⟩
    exact (a.pl n).2
  have hL : ∀ i, i ≤ B.R.m → IsSelfDualC _ (a.g.x i).L ∧
      ((a.g.x i).L : Set (Fin ((I.rec7 l Z).sp.X i).rank → (I.rec7 l Z).host.E)) = intVec _ _ :=
    fun i hi => ⟨(ha.x i hi).sd, Set.ext (haT.pinX.xs i hi).2.2⟩
  have key := GlobalTheory.T.rationalDatum_foldr_local_combinations (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ haT.pinX.std _ _ ((B.primes X).vT u) (B.primes X).vGs a.n _ hinj hmem
    (_root_.GlobalTheory.T.type_primes_disjoint' W hAll u) (fun n => (a.G n).cg j) Ξl hΞl (a.g.x j).L (a.g.x (j + 1)).L
    (hL j (by omega)).1 (hL (j + 1) hj).1 (hL j (by omega)).2 (hL (j + 1) hj).2 _ (a.g.vac j) _ hv0 hvl
    (fun e₀ he₀ => _root_.GlobalTheory.T.true_geometry_twist_reduction_alt W hAll u a ha haT t J hJ e₀ he₀ j hj (J.ι j α) (J.ι (j + 1) γ)) e he
  rw [← ha.gpin.dG j (by exact hj) _ hvT] at key
  have hCj : C j ≠ 0 := hC j (by omega)
  convert key using 2 with z
  simp only [xiOff, map_mul, hfac z]
  field_simp
end GlobalTheory.Fam
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumXiOffCommonStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ e, IsIdemSum e ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ, IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ e (fun z => C j * xiOff J.A j hj (J.ι j α) (J.ι (j + 1) γ) z) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j))) := by
  first | exact @_root_.GlobalTheory.Fam.ratDatum_xiOff_common_alt | exact _root_.GlobalTheory.Fam.ratDatum_xiOff_common_alt | (intros; apply _root_.GlobalTheory.Fam.ratDatum_xiOff_common_alt <;> assumption)
end
end
end
