module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleAdjointRationalPointPadicMatrix
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatStepOfChThOk
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatTermOfRatStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubAddLeSpread
public import Formalism.LocalToGlobal.Columns.TiedAtT
import Std.Tactic.BVDecide.Normalize.BitVec

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemHomAtGmap

section

@[expose] public section

noncomputable section

namespace GlobalTheory.KerT.Bar

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (InBox)

section Box

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    x ∈ homAt S (gmap g N) (gmap g' N') ↔ g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have := h P hP (g y) ((mem_localization_gmap _ _ _ _).2 (by simpa using hy))
    exact (mem_localization_gmap _ _ _ _).1 this
  · intro h P hP y hy
    have := h P hP (g.symm y) ((mem_localization_gmap _ _ _ _).1 hy)
    exact (mem_localization_gmap _ _ _ _).2 (by simpa using this)

theorem conj_osmul (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (c : 𝓞 E) (x : HomE E a b) :
    g'.symm.toLinearMap ∘ₗ (c • x) ∘ₗ g.toLinearMap = c • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine LinearMap.ext fun y => ?_
  exact equiv_osmul g'.symm c (x (g y))

theorem inBox_gmap {K : Type} [Field K] {S : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Ξ : HomE E a b → K} (h : InBox S cA cB N N' Ξ)
    (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    InBox S cA cB (gmap g N) (gmap g' N') fun x => Ξ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have h1 : (cA : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) ∈ homAt S N N' := h.1 _ hx
    change (cA : 𝓞 E) • x ∈ homAt S (gmap g N) (gmap g' N')
    rw [mem_homAt_gmap, conj_osmul]
    exact h1
  · rintro x _ ⟨z, hz, rfl⟩
    have h1 := h.2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ ⟨_, (mem_homAt_gmap S g g' N N' z).1 hz, rfl⟩
    change Ξ (g'.symm.toLinearMap ∘ₗ (x + (cB : 𝓞 E) • z) ∘ₗ g.toLinearMap) = _
    rw [LinearMap.add_comp, LinearMap.comp_add, conj_osmul]
    exact h1

end Box

variable {X : Fields}

theorem framed_gmap {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E n)} {fr : Frs X.E n SB}
    (h : Framed N fr) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Framed (gmap g N) (fun P : SB => g * fr P) := by
  intro P x
  rw [mem_localization_gmap, ← h P x]
  simp

theorem mem_valAt_gmap (w : HeightOneSpectrum (𝓞 X.K)) {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n)
    (L : Submodule (𝓞 X.E) (Sp X.E n)) (y : VV X.K lam) :
    y ∈ valAt w lam (gmap γ.1 L) ↔ ∃ z ∈ valAt w lam L, rhoVr X.emb lam (ufGL X.E n γ) z = y := by
  unfold valAt
  rw [delAtr_gmap, Formalism.BasicNotions.SkeletonIndexLemmas.localization_map₂]
  exact Iff.rfl

theorem rho_inv_apply {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ⁻¹) (rhoVr X.emb lam (ufGL X.E n γ) y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

theorem barTerm_of_std : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → RatTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), (∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet (E := Z.X.E) (n := Z.R.N i) (ST := Z.Pr.vT u) (SG := SG)) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet (E := Z.X.E) (n := Z.R.N (i + 1)) (ST := Z.Pr.vT u) (SG := SG')) (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ∃ y' ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.Lsh, term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y = ((Z.Pr.T u : Z.X.K) ^ (Z.X.f * ((Z.R.t + 1) / 2))) • y') → BarTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) w := by
  intro Z H s cc δ B χ cD sel S mu cst u i _ hyp hrat w hstd SG SG' d fr d' fr' Ξ₀ hfr hfr' hbox hint y hy
  obtain ⟨γ, hγ⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG d
  obtain ⟨γ', hγ'⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG' d'
  obtain ⟨y', hy', he⟩ := hstd (((γ, 1) : UF Z.X.E _ × GLG (E := Z.X.E) (n := _) (SG := SG)) • d) (fun P => γ.1 * fr P)
    (((γ', 1) : UF Z.X.E _ × GLG (E := Z.X.E) (n := _) (SG := SG')) • d') (fun P => γ'.1 * fr' P)
    (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap))
    ⟨fun P => hγ P.1 P.2, fun P => hγ' P.1 P.2⟩ (framed_gmap hfr γ.1) (framed_gmap hfr' γ'.1)
    (inBox_gmap hbox γ.1 γ'.1) (fun x => hint _) (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ) y) (by
      rw [DecoSet.smul_val, Deco.Lsh_act _ γ.2, mem_valAt_gmap]
      exact ⟨y, hy, rfl⟩)
  rw [DecoSet.smul_val, Deco.Lsh_act _ γ'.2, mem_valAt_gmap] at hy'
  obtain ⟨z, hz, rfl⟩ := hy'
  refine ⟨z, hz, ?_⟩
  rw [hrat d fr d' fr' Ξ₀ γ γ' hbox, LinearMap.comp_apply, LinearMap.comp_apply, rho_inv_apply, ← map_smul] at he
  have h2 := congrArg (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ'⁻¹)) he
  rwa [rho_inv_apply, rho_inv_apply] at h2

end GlobalTheory.KerT.Bar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundConjugatePrimePlaces

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open _root_.Formalism.L2.Col

local instance starFields (B : Base) : StarRing B.fields.E := B.fields.starE

theorem kerBar : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerBar (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  intro hJM hP B X I h hJ l Z u a hth i hi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hA : ColIn.A I = ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J)
      (ColIn.chi I) I.J.cD := by
    rw [ColIn.A, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  have hAl := GlobalTheory.KerT.alcoveAt_of_ok I.dat hH.ok u (i + 1) (Nat.succ_le_of_lt hi)
  have hRS := GlobalTheory.KerT.ratStep_of_chTh_ok B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob
    (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth hi
  rw [hA] at hRS
  have hRT : GlobalTheory.KerT.RatTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD)
      u i (i + 1) :=
    GlobalTheory.KerRat.ratTerm_of_ratStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) _ u i hX hPr
      h.sel_ok (h.T_mem u) hRS
  have hT := isTerm h u a hi
  intro w hw hseen b b' d d' F hF
  classical
  unfold OverT at hw
  have hw' : (((B.primes X).T u : ℕ) : 𝓞 B.fields.K) ∈ ((I.rec7 l Z).plEq w).asIdeal := by
    have h0 := Formalism.L2.Col.att_resChar_mem (I.rec7 l Z).what₂.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq w
    rw [hw] at h0
    exact h0
  have hs : ¬ seenC (B.primes X) u ((I.rec7 l Z).plEq w) := fun hc => by
    have h0 : decide (seenC (B.primes X) u ((I.rec7 l Z).plEq w)) = false := hseen
    simp [hc] at h0
  have hsb : seenBarC (B.primes X) u ((I.rec7 l Z).plEq w) := (seenC_or_seenBarC hX hPr u _ hw').resolve_left hs
  have hbar : GlobalTheory.KerT.BarTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD) u i (i + 1)
      ((I.rec7 l Z).plEq w) := GlobalTheory.KerT.Bar.barTerm_of_std I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hRT ((I.rec7 l Z).plEq w)
    (fun d fr d' fr' Ξ₀ => GlobalTheory.BarStd.barStd hJM hP I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
      (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hJa hAl
      ((I.rec7 l Z).plEq w) hsb d fr d' fr' Ξ₀)
  rw [← hA] at hbar
  obtain ⟨Ξ₀, hbox, hint, hfr, hfr', hk⟩ := hT b b' d d'
  have hk' := hk d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  rw [hk']
  have hF' : F ∈ GlobalTheory.KerT.valAt ((I.rec7 l Z).plEq w) (B.wts.lamTrue u i) d.1.1.deco.1.Lsh := hF
  obtain ⟨y', hy', he⟩ := hbar d.1.1.deco _ d'.1.1.deco _ Ξ₀ hfr hfr' hbox (hint _ hw') F hF'
  refine ⟨y', hy', he.trans ?_⟩
  have e1 : B.fields.f = (I.rec7 l Z).R.f := GlobalTheory.Mem.Base.fields_f B
  rw [e1]
  rfl

end GlobalTheory.LvT.Built.TrueLaws
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundConjugatePrimePlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

theorem _root_.GlobalTheory.T.trueChainKernels_bound_conjugatePrimePlaces : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerBar (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  first | exact @GlobalTheory.LvT.Built.TrueLaws.kerBar | exact GlobalTheory.LvT.Built.TrueLaws.kerBar | (intros; apply GlobalTheory.LvT.Built.TrueLaws.kerBar <;> assumption)
end
end
