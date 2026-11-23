module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTrans
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastRowInvFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameGlInt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mat_int {p : SplitPt D k} {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank)
    (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)} (h : β.IsLat L Λ) (g : GL (Fin S.rank) k)
    (hg : g • Λ = Λ) (r s : Fin S.rank) : (β.b * g.val * β.b') r s ∈ 𝒪[k] := by
  have hmem : ∀ x, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := fun x => by
    rw [h x, GlobalTheory.SeeSaw.StdOff.mem_latV_int hL]
    exact forall_congr' fun r =>
      ((p.int_iff _).trans (and_iff_right (GlobalTheory.SeeSaw.StdOff.sec_mem_idAt p _)).symm).symm
  have h1 : β.b' *ᵥ Pi.single s 1 ∈ Λ := (hmem _).2 fun r => by
    rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 : g • (β.b' *ᵥ Pi.single s 1) ∈ Λ := hg ▸ Submodule.smul_mem_pointwise_smul _ _ _ h1
  have h3 := (hmem _).1 h2 r
  convert h3 using 1
  rw [show g • (β.b' *ᵥ Pi.single s 1) = g.val *ᵥ (β.b' *ᵥ Pi.single s 1) from rfl, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    GlobalTheory.AdForm.finM V hn (g * h) = GlobalTheory.AdForm.finM V hn g * GlobalTheory.AdForm.finM V hn h := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt, Matrix.map_mul, Matrix.submatrix_mul_equiv]

theorem prF_finM (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    {n : ℕ} (hn : V.rank = n) (g : GA D V) (r s : Fin n) :
    q.prF he (GlobalTheory.AdForm.finM V hn g r s) = (Formalism.L2.Theta.mt V g).map q.pr ((finCongr hn).symm r) ((finCongr hn).symm s) := by
  simp [GlobalTheory.AdForm.finM, Matrix.reindex_apply, SplitPt.prF_toEAf]

theorem finM_one (V : HSp D) {n : ℕ} (hn : V.rank = n) : GlobalTheory.AdForm.finM V hn 1 = 1 := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt]

end GlobalTheory.FrameGlInt

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



theorem exists_int (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) (S : HSp D)
    {n : ℕ} (hn : S.rank = n) (hgram : S.gram.reindex (finCongr hn) (finCongr hn) = 1) {L : Lat S}
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)}
    (hlat : β.IsLat L Λ) (g : GL (Fin S.rank) k) (hgl : g • Λ = Λ) :
    ∃ δ : GL (Fin n) (GlobalTheory.AdForm.EF D), δ.1 = GlobalTheory.AdForm.finM S hn (β.gl g) ∧
      δ ∈ Formalism.UG.UPts (sigD D) (1 : Matrix (Fin n) (Fin n) D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  obtain ⟨⟨x, hx0⟩, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem S hn _ hgram.symm (β.gl g)
  refine ⟨x, hx, hx0, ?_⟩
  have hgl' : g⁻¹ • Λ = Λ := by
    conv_lhs => rw [← hgl]
    exact inv_smul_smul g _
  have hcomp : ∀ h : GL (Fin S.rank) k, h • Λ = Λ → ∀ r s,
      toEAf D p.e * GlobalTheory.AdForm.finM S hn (β.gl h) r s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro h hh r s
    rw [← p.prF_mem_iff he]
    have e1 := prF_finM p he S hn (β.gl h) r s
    rw [β.gl_mat h] at e1
    exact e1 ▸ mat_int hL β hlat h hh _ _
  set σ := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) with hσ

  have hu0 : Formalism.UG.cT σ x.1 * ((1 : Matrix (Fin n) (Fin n) D.host.E).map
      (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) * x.1 =
      (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := hx0
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hu0
  have hinvM : (x⁻¹).1 = Formalism.UG.cT σ x.1 := by
    calc (x⁻¹).1 = (Formalism.UG.cT σ x.1 * x.1) * (x⁻¹).1 := by rw [hu0, one_mul]
      _ = _ := by rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

  have hxi : (x⁻¹).1 = GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) := by
    have h1 : x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) = 1 := by
      rw [hx, ← finM_mul, ← map_mul, mul_inv_cancel, map_one, finM_one]
    calc (x⁻¹).1 = (x⁻¹).1 * (x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨hf, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D p.e PP he
  have hσmem : ∀ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, σ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun y hy => GlobalTheory.Mem.Col2.sigR_mem_rInt D.sp.cm hy
  have hσσ : ∀ y, σ (σ y) = y := Formalism.L2.DIV.sigR_sigR D.sp.cm
  have hcA : toEAf D (cA D p.e) = σ (toEAf D p.e) := GlobalTheory.AdForm.RdVal.toEAf_sig p.e
  have hint : ∀ r r', x.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro r r'
    have hs := congrArg (toEAf D) (β.gl_supp g ((finCongr hn).symm r) ((finCongr hn).symm r'))
    have hxr : x.1 r r' = toEAf D (Formalism.L2.Theta.mt S (β.gl g) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      rw [hx]; rfl
    have hcm : toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [Matrix.one_apply]; split_ifs
      · rw [RingHom.map_one]; exact one_mem _
      · rw [RingHom.map_zero]; exact zero_mem _
    rw [Matrix.sub_apply, RingHom.map_mul, RingHom.map_sub, RingHom.map_add (f := _), hcA, ← hxr] at hs
    have hdec : x.1 r r' = toEAf D p.e * x.1 r r' + σ (toEAf D p.e * (x⁻¹).1 r' r) +
        (1 - toEAf D p.e - σ (toEAf D p.e)) *
          toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      have e2 : σ (toEAf D p.e * (x⁻¹).1 r' r) = σ (toEAf D p.e) * x.1 r r' := by
        rw [hinvM, map_mul]
        show σ (toEAf D p.e) * σ (σ (x.1 r r')) = _
        rw [hσσ]
      rw [e2]
      linear_combination (-1 : GlobalTheory.AdForm.EF D) * hs
    rw [hdec]
    refine add_mem (add_mem ?_ ?_) (mul_mem (sub_mem (sub_mem (one_mem _) hf) (hσmem _ hf)) hcm)
    · exact hx ▸ hcomp g hgl r r'
    · exact hσmem _ (hxi ▸ hcomp g⁻¹ hgl' r' r)
  exact ⟨hint, fun r r' => by
    rw [hinvM]
    exact hσmem _ (hint r' r)⟩

end GlobalTheory.FrameGlInt

theorem GlobalTheory.AdForm.frameGl_int : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (s : 𝓀[k]ˣ), g • Q j i = s • Q j i →
    ∃ δ : TC.GA B (B.R.N j), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) ∧ δ ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) ∧ (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) := by
  intro B X I hOk hPins l Z u a k _ _ _ _ ι p β Q L hStd j hj i v hIdem g s hgs
  have hg1 : gramN (I.rec7 l Z) j hj = 1 := ((TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 j hj).1
  obtain ⟨-, hT⟩ := hStd
  obtain ⟨hL, hT'⟩ := hT j hj
  obtain ⟨hlat, -⟩ := hT' i
  have hgl : g • (Q j i).lat = (Q j i).lat := by
    have := congrArg GlobalTheory.LatPair.Pair.lat hgs
    rwa [GlobalTheory.LatPair.Pair.smul_lat, GlobalTheory.LatPair.Pair.dia_lat] at this
  obtain ⟨δ, h1, h2, h3, h4⟩ := GlobalTheory.FrameGlInt.exists_int (p i) hIdem _ (rankN (I.rec7 l Z) j hj) hg1 hL (β j i) hlat g hgl
  exact ⟨δ, h1, h2, h3, h4⟩

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameImageTrivialOffLevelPrime

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.FrameTriv

theorem frame_trivial_off : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (δ : TC.GA B (B.R.N j)), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    ∀ w : HeightOneSpectrum (𝓞 B.fields.E), (w ∈ (B.primes X).vGs ∨ w ∈ I.SQ ∨ (w ∈ (B.primes X).vT u ∧ w ≠ v.1)) →
      ∀ r r', adAt B.host.F w ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
  intro B X I hI _ l Z u a k _ _ _ _ ι p β Q L _ j hj i v hidem g δ hδ w hw r r'
  classical
  have hPr : (B.primes X).Ok := l.pr
  have hv : (p i).v = v.1.under (𝓞 B.host.F) := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under (p i) hidem
  have hvT : v.1 ∈ (B.primes X).vT u := v.2
  have hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ v.1.asIdeal := T_mem_vT hPr u ⟨v.1, hvT⟩
  have hne : w.under (𝓞 B.host.F) ≠ (p i).v := by
    intro hwv
    rw [hv] at hwv
    have hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have h1 : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (w.under (𝓞 B.host.F)).asIdeal := by
        rw [hwv]
        show algebraMap _ (𝓞 B.fields.E) _ ∈ v.1.asIdeal
        rw [map_natCast]
        exact hTv
      have h2 : algebraMap _ (𝓞 B.fields.E) (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ w.asIdeal := h1
      rwa [map_natCast] at h2
    rcases hw with h | h | ⟨h, hwne⟩
    · exact Formalism.L2.Col.T_notMem_vGs hPr u ⟨w, h⟩ hTw
    · have hg := (GlobalTheory.Mem.LevTwist.good_of_mem hI h).2
      have e := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) w (hPr.T_prime u)).2 hTw
      refine hg.2.2 ?_
      rw [e]
      exact hI.T_mem u
    · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (D := I.rec7 l Z) hwv with e | e
      · exact hwne e
      · have hT0 : (B.primes X).piT u ≠ 0 := fun h0 => by
          have := hPr.piT_norm u
          rw [h0, zero_mul] at this
          exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
        have a1 : (B.primes X).piT u ∈ v.1.asIdeal := (Formalism.L2.Col.mem_divs hT0 _).1 hvT
        have a2 : (B.primes X).piT u ∈ w.asIdeal := (Formalism.L2.Col.mem_divs hT0 _).1 h
        rw [e] at a2
        have a3 : B.fields.conjO ((B.primes X).piT u) ∈ v.1.asIdeal := (Formalism.L2.Col.mem_conjP _ _).1 a2
        obtain ⟨x, y, hxy⟩ := hPr.piT_cop u
        have : (1 : 𝓞 B.fields.E) ∈ v.1.asIdeal := by
          rw [← hxy]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a3)
        exact v.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hb : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F))) δ = 1 :=
    GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one (I.rec7 l Z) k (p i) ((I.rec7 l Z).sp.X j) _ (β j i) g _ (rankN (I.rec7 l Z) j hj) δ hδ _ hne
  have hb' : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F))) δ⁻¹ = 1 := by
    rw [map_inv, hb, inv_one]
  have h2 : Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F)) ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
    have := congrArg (fun x : GL (Fin (B.R.N j)) _ => x.1 r r') hb'
    simp only [Units.val_one, Matrix.one_apply] at this
    exact this
  have h3 : Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F)) ((δ⁻¹).1 r r' - if r = r' then 1 else 0) = 0 := by
    rw [map_sub, h2]
    split_ifs <;> simp
  have h4 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff B.host.F B.host.E _ _).1.1 h3 w rfl
  rw [map_sub, sub_eq_zero] at h4
  rw [h4]
  split_ifs <;> simp

end GlobalTheory.AdForm.FrameTriv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameImageTrivialOffLevelPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameImage_trivial_off_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (δ : TC.GA B (B.R.N j)), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    ∀ w : HeightOneSpectrum (𝓞 B.fields.E), (w ∈ (B.primes X).vGs ∨ w ∈ I.SQ ∨ (w ∈ (B.primes X).vT u ∧ w ≠ v.1)) →
      ∀ r r', adAt B.host.F w ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
  first | exact @GlobalTheory.AdForm.FrameTriv.frame_trivial_off | exact GlobalTheory.AdForm.FrameTriv.frame_trivial_off | (intros; apply GlobalTheory.AdForm.FrameTriv.frame_trivial_off <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueEqZeroIffValLt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

theorem residue_eq_zero_iff_val_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : 𝒪[k]) : residue 𝒪[k] t = 0 ↔ valuation k (t : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem resField_equiv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k]) ∧ ∃ ρ : 𝓀[k] ≃+* (𝓞 D.host.E ⧸ PP.asIdeal), ∀ (x : 𝓞 D.host.E) (t : 𝒪[k]), (t : k) = q.pr (incA D (x : D.host.E)) → ρ (residue 𝒪[k] t) = Ideal.Quotient.mk PP.asIdeal x := by
  intro D k _ _ _ _ q PP he
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  have hmem : ∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := fun x => by
    rw [q.pr_mem_iff]
    exact mul_mem hint (Formalism.L2.DIV.oToS D.host.F D.host.E x).2
  refine ⟨hmem, ?_⟩
  let ψ : 𝓞 D.host.E →+* 𝒪[k] :=
    ((q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k] hmem
  have hψ : ∀ x, (ψ x : k) = q.pr (incA D (x : D.host.E)) := fun x => rfl
  let φ : 𝓞 D.host.E →+* 𝓀[k] := (residue 𝒪[k]).comp ψ
  have hker : RingHom.ker φ = PP.asIdeal := by
    ext x
    have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
        toEAf D (incA D (x : D.host.E)) := rfl
    rw [RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff_val_lt, hψ, q.mem_iff_val_lt he, e1, prF_toEAf]
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    set z : EAf D := toEAf D (q.sec a) with hz
    have hprz : q.prF he z = a := by rw [hz, prF_toEAf, q.pr_sec]
    have hoff : (1 - toEAf D q.e) * z = 0 := by
      have he1 : toEAf D q.e * z = z := by
        rw [hz, ← RingHom.map_mul, ← q.sec_pr, q.pr_sec]
      rw [sub_mul, one_mul, he1, sub_self]
    have hzint : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      (q.mem_intAf_iff he z).2 ⟨by rw [hoff]; exact zero_mem _, by rw [hprz]; exact a.2⟩
    obtain ⟨x, hx0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot ⟨z, hzint⟩
    have hx : (⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x ∈
        Formalism.L2.DIV.idS D.host.F PP.asIdeal := hx0
    have hv := q.val_lt_of_mem_idS he hx
    refine ⟨x, ?_⟩
    show residue 𝒪[k] (ψ x) = residue 𝒪[k] a
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_val_lt]
    have e1 : (((⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = z - toEAf D (incA D (x : D.host.E)) := rfl
    rw [e1, map_sub, hprz, prF_toEAf] at hv
    have e2 : ((ψ x - a : 𝒪[k]) : k) = -((a : k) - q.pr (incA D (x : D.host.E))) := by
      rw [AddSubgroupClass.coe_sub, hψ]; ring
    rw [e2, Valuation.map_neg]; exact hv
  refine ⟨((Ideal.quotEquivOfEq hker).symm.trans (RingHom.quotientKerEquivOfSurjective hsurj)).symm, ?_⟩
  intro x t ht
  have htx : t = ψ x := Subtype.ext (by rw [ht, hψ])
  rw [RingEquiv.symm_apply_eq, htx]
  rfl

end GlobalTheory.FinPl.SplitPt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartPointRightTranslateStabilizerSplitPla

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaChart

theorem decoratedLattice_unitScale_functional_keeps_frames {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y}
    (p : PtY (X := X) (n := n) ST SG Q y) (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (P' : HeightOneSpectrum (𝓞 X.E)) :
    ptFr (p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco)).1.1 P' = ptFr p.1.1 P' := by
  by_cases h : (∀ (P₁ : Q) (x : Formalism.L2.Col.Sp X.E n), p.1.1.1.2 P₁ x ∈ (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.at P₁.1 ↔
      x ∈ Formalism.L2.Col.stdAt X.E n P₁.1) ∧ p.1.2 ∈ y.ys (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.N
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) =
        ⟨(⟨(Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    unfold ptFr
    rfl
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) = p := dif_neg h
    rw [e]

theorem finM_mul' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem ptOf_gl_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b (c : {c // A.chOf j c = b}), ∃ e : 𝓀[k]ˣ ≃ ((I.atT l u a).Fv v)ˣ, ∀ s,
        ∃ z : TC.GA B (B.R.N j),
          z.1 = finM _ (rankN (I.rec7 l Z) j hj) (A.h j b c * (β j i).gl (g s)) ∧
          TC.PtOf (z * A.kb j b) (extTo I.SQ (((I.atIn u a).A j).diaPt v (e s) c.1).1.1) := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj i v hv g hg b c
  obtain ⟨c, rfl⟩ := c
  obtain ⟨-, ρ, hρ⟩ := GlobalTheory.FinPl.SplitPt.resField_equiv (I.rec7 l Z) k (p i) v.1 hv
  refine ⟨(Units.mapEquiv ρ.toMulEquiv).toEquiv, fun s => ?_⟩
  obtain ⟨δ, hδ, huni, hint, hint'⟩ := GlobalTheory.AdForm.frameGl_int I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) s (hg s)
  have htriv := GlobalTheory.T.frameImage_trivial_off_levelPrime I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) δ hδ
  have hrow := GlobalTheory.AdForm.lastRow_inv_frame I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv ρ hρ (g s) s (hg s) δ hδ hint'
  have hR := hA.reads j hj
  let y : TC.GA B (B.R.N j) := ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1
  refine ⟨y * δ, ?_, ?_⟩
  · rw [Units.val_mul, hδ, finM_mul', (hA.h j hj _ ⟨c, rfl⟩).2]
    rfl
  · obtain ⟨p0, hk0, hN0⟩ := hR.k_std (A.chOf j c)
    have hkc := hk0.lat
    rw [hN0] at hkc
    refine GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt _ _ _ _ _ _ _ y δ (A.kb j (A.chOf j c)) (extTo I.SQ ((I.stp u a j).rep c).1.1) _
      ⟨v.1, v.2⟩ ((Units.mapEquiv ρ.toMulEquiv) s) _ (hR.pt c) hk0.uni huni hkc hint hint' htriv
      (fun r r' hr => hR.k_T (A.chOf j c) ⟨v.1, v.2⟩ r r' hr) (fun r r' hr => hrow r r' hr) ?_ ?_
    · rw [extTo_deco, extTo_deco]
      exact GlobalTheory.Mem.Col2.TwAtStd.diaPt_deco B X I u a j ⟨v.1, v.2⟩ _ c
    · funext P'
      rw [extTo_fr, extTo_fr]
      exact decoratedLattice_unitScale_functional_keeps_frames ((I.stp u a j).rep c) ⟨v.1, v.2⟩ _ P'.1

end GlobalTheory.AdForm.DiaChart

end
end
end
