module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitFormUnitaryIntegralEntriesOfLevelLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentIntegralOfFiniteMatrixIntegral

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinIntBridge

theorem comm_symm_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] v.adicCompletion F}
    (ha : a ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) :
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm a ∈ GlobalTheory.AdelicU.intLoc F E v := by
  have hle : Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ≤
      (GlobalTheory.AdelicU.intLoc F E v).comap
      ((Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F ⊗[F] E) := by
    unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩)
    · obtain ⟨x, rfl⟩ := RingHom.mem_range.1 (show e ∈ (algebraMap (𝓞 E) E).range from he)
      simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (one_mem _) x
    · simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (a := b) hb 1
  exact hle ha

theorem prV_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (y : AF F ⊗[F] E) :
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).symm (Formalism.UG.prV (E := E) v
      (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y))) =
      Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin F v) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_intLoc_of_finM : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D)), GlobalTheory.AdForm.finM V hn κ = x.1 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 i j ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) → ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v κ)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D V n hn κ x hx v h i j
  have h1 := comm_symm_mem v (h (finCongr hn i) (finCongr hn j))
  have h2 : (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 (finCongr hn i) (finCongr hn j) =
      Formalism.UG.prV (E := D.host.E) v (toEAf D (Formalism.L2.Theta.mt V κ i j)) := by
    change Formalism.UG.prV (E := D.host.E) v (x.1 (finCongr hn i) (finCongr hn j)) = _
    rw [← hx]
    simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  rw [h2] at h1
  have h3 := prV_gen (F := D.host.F) (E := D.host.E) v (Formalism.L2.Theta.mt V κ i j)
  exact (congrArg (· ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) h3).mp h1

end GlobalTheory.FinIntBridge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentIntegralOfFiniteMatrixIntegralStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localComponent_integral_of_finiteMatrix_integral : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D)), GlobalTheory.AdForm.finM V hn κ = x.1 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 i j ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) → ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v κ)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  first | exact @GlobalTheory.FinIntBridge.mem_intLoc_of_finM | exact GlobalTheory.FinIntBridge.mem_intLoc_of_finM | (intros; apply GlobalTheory.FinIntBridge.mem_intLoc_of_finM <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeForward

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LatFwd

theorem finM_inv_eq {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D))
    (h : GlobalTheory.AdForm.finM V hn κ = x.1) : GlobalTheory.AdForm.finM V hn κ⁻¹ = (x⁻¹).1 := by
  subst hn
  have e : GlobalTheory.AdForm.finM V rfl κ * GlobalTheory.AdForm.finM V rfl κ⁻¹ = 1 := by
    have e1 : ∀ g, GlobalTheory.AdForm.finM V rfl g = (mt V g).map (toEAf D) := fun g => rfl
    have e2 : mt V κ * mt V κ⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [e1, e1, ← Matrix.map_mul, e2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h] at e
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

theorem proj_mem_stabLoc_std {D : D7} (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hM : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v)
    (hM' : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g⁻¹)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.stdLattice D.host.E V.rank) v := by
  rw [map_inv, map_inv] at hM'
  set M := GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)
  have hint : ∀ (N : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)),
      (∀ i j, N i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ z : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ i, z i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ i, (N *ᵥ z) i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
    fun N hN z hz i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hN i j) (hz j)
  refine GlobalTheory.AdelicU.mem_stabLoc.2 fun z => ?_
  simp only [GlobalTheory.AdelicU.mem_latLoc_stdLattice]
  refine ⟨fun hz => hint _ hM z hz, fun hz => ?_⟩
  have e : (M⁻¹).1 *ᵥ (M.1 *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e]
  exact hint _ hM' _ hz

end GlobalTheory.FamTrace.LatFwd

namespace GlobalTheory.FamTrace.LatFwd


end GlobalTheory.FamTrace.LatFwd

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeForwardPreservesBase

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace.LatFwd
end GlobalTheory.FamTrace.LatFwd
namespace GlobalTheory.FamTrace.LatFwd

theorem lattice_forward_preserves_base_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => _root_.True) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hU
  have hs := hA.tr.std.some u
  obtain ⟨k, hk⟩ := hs.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hlb := hk.lb ()
  have hg : Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 :=
    ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hA.tr.ok hA.tr.pins.some l Z).2.2.2 0 (Nat.zero_le _)).1
  have hfg : ((a.g.x 0).L).FG := by
    haveI : Submodule.IsLattice _ (a.g.x 0).L := (ha.x 0 (Nat.zero_le _)).sd.1
    exact Submodule.IsLattice.fg (A := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (a.g.x 0).L
  have hne : X.piT u ≠ 0 := by
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hne' : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h => hne (by exact_mod_cast h)
  have hσ : ∀ x, Formalism.L2.Forms.sigD (I.rec7 l Z) (Formalism.L2.Forms.sigD (I.rec7 l Z) x) = x := fun x => star_star x
  have hΛ : ∀ x, x ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb ↔ ∀ j : Fin _, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = (r : (I.rec7 l Z).host.E) ∧ (j.1 + 1 = _ → X.piT u ∣ r) :=
    fun x => hlb x
  have hloc : ∀ v, ∀ g ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v, ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (Formalism.UG.intOE (I.rec7 l Z).host.E) (v.adicCompletionIntegers (I.rec7 l Z).host.F).toSubring :=
    fun v g hgv => GlobalTheory.T.unitFormUnitary_integralEntries_of_levelLattice _ _ _ hσ _ _ hg _ hne' _ hΛ v g ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc_lev v hgv)
  have hyv := (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U_eq y.1).1 hU).2
  have hyinv := finM_inv_eq _ _ κ y.1 hy
  refine GlobalTheory.FinPl.KOpen.moves_of_levelOpen _ _ hfg _ ?_
  clear hs hk hlb row col hc
  have hL : (a.g.x 0).L = GlobalTheory.AdelicU.stdLattice (I.rec7 l Z).host.E ((I.rec7 l Z).sp.X 0).rank := by
    ext z
    rw [(hat.pinX.xs 0 (Nat.zero_le _)).2.2 z]
    simp only [GlobalTheory.AdForm.intVec, Set.mem_setOf_eq, GlobalTheory.AdelicU.stdLattice, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, LinearMap.mem_range, Algebra.linearMap_apply]
    exact forall_congr' fun k => ⟨fun hk => ⟨⟨_, hk⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe⟩
  rw [GlobalTheory.AdelicU.levelOpen, Subgroup.mem_iInf]
  intro v
  rw [Subgroup.mem_comap, hL]
  have e2 : ∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y.1)⁻¹).1 i j ∈ Formalism.UG.tensInt (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (Formalism.UG.intOE (I.rec7 l Z).host.E) (v.adicCompletionIntegers (I.rec7 l Z).host.F).toSubring := by
    rw [map_inv]; exact hloc v _ (inv_mem (hyv v))
  exact proj_mem_stabLoc_std _ κ v (GlobalTheory.T.localComponent_integral_of_finiteMatrix_integral _ _ _ _ κ y.1 hy v (hloc v _ (hyv v)))
    (GlobalTheory.T.localComponent_integral_of_finiteMatrix_integral _ _ _ _ κ⁻¹ (y.1)⁻¹ hyinv v e2)
end GlobalTheory.FamTrace.LatFwd
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeForwardPreservesBaseStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_lattice_forward_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => _root_.True) := by
  first | exact @_root_.GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base_alt | exact _root_.GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base_alt | (intros; apply _root_.GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base_alt <;> assumption)
end
end
end
