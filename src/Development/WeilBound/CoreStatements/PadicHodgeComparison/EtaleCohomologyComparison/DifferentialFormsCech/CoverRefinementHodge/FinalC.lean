module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.FormToCOBijectiveI
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.CovRefine
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorId
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.PfPullC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeDegenerationNatural
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.AffineOpenCaps.GlobTerm
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.InjectiveSequenceLift

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovOfLocal

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qm13.cov_of_local :
    ∀ {O : Type} [inst : CommRing O] {X : AlgebraicGeometry.Scheme} (Q : X.Opens → Prop)
    (q : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of O)) [AlgebraicGeometry.IsSeparated q]
    [AlgebraicGeometry.QuasiCompact q],
    (∀ (x : ↥X), ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ Q V ∧ Nonempty (CrystallineSemistableComparison.Pb.Coord q V d)) →
      ∃ (U : CrystallineSemistableComparison.Pb.Cov q),
        ∀ (α : U.ι),
          Q
            (U.U
              α) := by
  intro O _ X Q q _ _ h
  choose V d hx hQ hc using h
  have : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace q
  have : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from q]; infer_instance⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨⟨s, fun a => V a, fun a => d a, fun a => (hc a).some, ?_, fun S hS => ?_⟩, fun a => hQ _⟩
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  · exact AlgebraicGeometry.IsAffineOpen.biInf (S : Set s) S.finite_toSet hS
      fun a _ => (hc a).some.affine
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.NeedPf

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Om.Nt2

theorem cov_of_local' {O : Type} [CommRing O] {X : Scheme.{0}} (Q : X.Opens → Prop) (q : X ⟶ Spec (CommRingCat.of O))
    [IsSeparated q] [QuasiCompact q] (h : ∀ x : X, ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ Q V ∧ Nonempty (Pb.Coord q V d)) :
    ∃ U : Pb.Cov q, ∀ α, Q (U.U α) :=
  _root_.UpperTheory.Reformulated.B.Qm13.cov_of_local Q q h

theorem cov_refine : CovRefine := by
  intro K _ X q _ _ _ κ V hV
  refine cov_of_local' (fun W => ∃ k, W ≤ V k) q fun x => ?_
  have hx : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨W, hW, hxW, hWk⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := V k) (x := x) hk
  have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ W le_top).hom :=
    RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hW le_top)
  obtain ⟨f, hf, hst⟩ :=
    GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth RingHom.isStandardSmooth_respectsIso q hW h hxW
  obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
  exact ⟨_, n, hf, ⟨k, fun y hy => hWk (X.basicOpen_le f hy)⟩, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hW f g hg he⟩

theorem pullH_id : PullHId := fun q h a n x => GlobalTheory.CompanionTheory.HodgePull.pullH_id _ _ q a n x

theorem pullC_id : PullCId := fun q h a j x => GlobalTheory.HodgeCoh.hodgePull_id q a j x

end CrystallineSemistableComparison.Om.Nt2
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeDegenerationNaturalStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.cech_hodge_degeneration_natural : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] (cechH (Fk q U a) (Vk q U a) a).cx.H j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι) (a : ℕ)
      (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T))
      (hτ : ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
      (j : ℕ) (c : (cechH (Fk p W a) (Vk p W a) a).X j) (h0 : (cechH (Fk p W a) (Vk p W a) a).cx.d j c = 0)
      (h1 : (cechH (Fk q U a) (Vk q U a) a).cx.d j (fun i =>
        (morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
          (U' := capT (Vk q U a) i) fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      HT.pullH u hu a (a + j) ((e p W a j).symm ((cechH (Fk p W a) (Vk p W a) a).cx.cls c h0)) =
        (e q U a j).symm ((cechH (Fk q U a) (Vk q U a) a).cx.cls _ h1) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlobSite.glob_site | exact GlobalTheory.CompanionTheory.OmGlobSite.glob_site | (intros; apply GlobalTheory.CompanionTheory.OmGlobSite.glob_site <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompat

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.OmGlobPush

theorem push_kc : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  intro K _ X Y q p u hu U W τ hτ a
  have key : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)) (α : U.ι),
      CrystallineSemistableComparison.Pb.InU (U.U α) T → CrystallineSemistableComparison.Pb.InU (W.U (τ α)) ((pullM u hu a).G.obj T) := by
    intro T α h
    have h0 : U.U α ≤ u ⁻¹ᵁ W.U (τ α) := by
      have h1 := hτ 0 (fun _ => α)
      simpa [CrystallineSemistableComparison.Pb.capO] using h1
    unfold CrystallineSemistableComparison.Pb.InU at h ⊢
    change ⊤ ≤ (TopologicalSpace.Opens.map (pt T ≫ u).base).obj (W.U (τ α))
    exact h.trans ((TopologicalSpace.Opens.map (pt T).base).monotone h0)
  have ktf : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)),
      CrystallineSemistableComparison.Pb.TF 1 (a + 1) T → CrystallineSemistableComparison.Pb.TF 1 (a + 1) ((pullM u hu a).G.obj T) := by
    intro T h
    exact h
  refine ⟨fun T hT => ?_, fun α T hT => ?_⟩
  · obtain ⟨hTF, V, ⟨α, rfl⟩, hV⟩ := hT
    exact ⟨ktf T hTF, W.U (τ α), ⟨τ α, rfl⟩, key T α hV⟩
  · exact key T.obj α hT

end GlobalTheory.CompanionTheory.OmGlobPush
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompatStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.pullback_cover_star_compat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlobPush.push_kc | exact GlobalTheory.CompanionTheory.OmGlobPush.push_kc | (intros; apply GlobalTheory.CompanionTheory.OmGlobPush.push_kc <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.HodgeCechComparison

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob

namespace CrystallineSemistableComparison.Om.GlobPf2

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ)
  (t : ∀ n (i : Fin (n + 1) → U.ι), HU (Fk q U a) (capT (Vk q U a) i) a ≃ₗ[K] OmU q (capO U.U i) a)

def tH (ht : ∀ m n (i : Fin (n + 1) → U.ι) (θ : Fin (m + 1) → Fin (n + 1)) (x : HU (Fk q U a) (capT (Vk q U a) (i ∘ θ)) a),
      t n i ((resU (Fk q U a) (U := capT (Vk q U a) (i ∘ θ)) (V := capT (Vk q U a) i) fun T hT k => hT (θ k)).pull a x) =
        formRes q (capO_comp U.U i θ) a (t m (i ∘ θ) x)) :
    Cx.Hom (cechH (Fk q U a) (Vk q U a) a).cx (formCos q U.U a).cx (RingHom.id K) where
  f n := LinearMap.pi fun i => (t n i).toLinearMap.comp (LinearMap.proj i)
  comm n x := by
    funext i
    let e := (t (n + 1) i).toAddEquiv.toAddMonoidHom
    have key : ∀ k : Fin (n + 2), (formCos q U.U a).δ n k (fun i' => t n i' (x i')) i =
        e ((cechH (Fk q U a) (Vk q U a) a).δ n k x i) := fun k =>
      (ht n (n + 1) i k.succAbove (x (i ∘ k.succAbove))).symm
    change (formCos q U.U a).d n (fun i' => t n i' (x i')) i =
      e ((cechH (Fk q U a) (Vk q U a) a).d n x i)
    rw [Cos.d_apply, Cos.d_apply, Finset.sum_apply, Finset.sum_apply, map_sum e]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Pi.smul_apply, Pi.smul_apply, e.map_zsmul, key k]

theorem tH_bij (ht) (n : ℕ) : Function.Bijective ((tH q U a t ht).f n) := by
  refine ⟨fun x y h => funext fun i => (t n i).injective (congrFun h i), fun y => ⟨fun i => (t n i).symm (y i), ?_⟩⟩
  funext i
  exact (t n i).apply_symm_apply (y i)

end

theorem cls_congr0 {R : Type} [CommRing R] (L : Cx.{0} R) (n : ℕ) (x y : L.X n) (hx : L.d n x = 0) (hy : L.d n y = 0)
    (h : x = y) : L.cls x hx = L.cls y hy := by
  subst h; rfl

theorem glob_iso : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] (formCos q U.U a).cx.H j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
      (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a j : ℕ) (c : (formCos p W.U a).X j)
      (h0 : (formCos p W.U a).cx.d j c = 0)
      (h1 : (formCos q U.U a).cx.d j (fun i => formRes q (hτ j i) a (formPull hu (capO W.U (τ ∘ i)) a (c (τ ∘ i)))) = 0),
      HT.pullH u hu a (a + j) ((e p W a j).symm ((formCos p W.U a).cx.cls c h0)) =
        (e q U a j).symm ((formCos q U.U a).cx.cls _ h1) := by
  intro K _ _
  obtain ⟨e1, he1⟩ := GlobalTheory.T.cech_hodge_degeneration_natural K
  obtain ⟨t, htr, htp⟩ := GlobalTheory.CompanionTheory.OmGlobTerm.AssemblyHe1.term K
  let φ : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a : ℕ),
      Cx.Hom (cechH (Fk q U a) (Vk q U a) a).cx (formCos q U.U a).cx (RingHom.id K) := fun q _ U a =>
    tH q U a (t q U a) fun m n i θ x => htr q U a m n i θ x
  refine ⟨fun q _ U a j => (e1 q U a j).trans
    (LinearEquiv.ofBijective ((φ q U a).mapH j) (P.mapH_bij (φ q U a) (fun n => tH_bij q U a (t q U a) (fun m n i θ x => htr q U a m n i θ x) n) j)), ?_⟩
  intro X Y q p _ _ u hu U W τ hτ a j c h0 h1
  obtain ⟨hG, hτ'⟩ := GlobalTheory.T.pullback_cover_star_compat q p u hu U W τ hτ a

  let c₀ : (cechH (Fk p W a) (Vk p W a) a).X j := fun i => (t p W a j i).symm (c i)
  have hc₀ : (φ p W a).f j c₀ = c := funext fun i => (t p W a j i).apply_symm_apply (c i)
  have h0' : (cechH (Fk p W a) (Vk p W a) a).cx.d j c₀ = 0 := by
    refine (tH_bij p W a (t p W a) (fun m n i θ x => htr p W a m n i θ x) (j + 1)).1 ?_
    rw [map_zero, ← (φ p W a).comm, hc₀, h0]

  let c₁ : (cechH (Fk q U a) (Vk q U a) a).X j := fun i =>
    (morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
      (U' := capT (Vk q U a) i) fun T hT k => hτ' (i k) T (hT k)).pull a (c₀ (τ ∘ i))
  have hc₁ : (φ q U a).f j c₁ = fun i => formRes q (hτ j i) a (formPull hu (capO W.U (τ ∘ i)) a (c (τ ∘ i))) := by
    funext i
    refine (htp q p u hu U W τ hτ a hG j i (fun T hT k => hτ' (i k) T (hT k)) (c₀ (τ ∘ i))).trans ?_
    exact congrArg _ (congrArg _ ((t p W a j (τ ∘ i)).apply_symm_apply (c (τ ∘ i))))
  have h1' : (cechH (Fk q U a) (Vk q U a) a).cx.d j c₁ = 0 := by
    refine (tH_bij q U a (t q U a) (fun m n i θ x => htr q U a m n i θ x) (j + 1)).1 ?_
    rw [map_zero, ← (φ q U a).comm, hc₁, h1]
  have key := he1 q p u hu U W τ a hG hτ' j c₀ h0' h1'
  have eY : (LinearEquiv.ofBijective ((φ p W a).mapH j) (P.mapH_bij (φ p W a) (fun n => tH_bij p W a (t p W a) (fun m n i θ x => htr p W a m n i θ x) n) j)).symm
      ((formCos p W.U a).cx.cls c h0) = (cechH (Fk p W a) (Vk p W a) a).cx.cls c₀ h0' := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, P.mapH_cls (φ p W a) j c₀ h0' (by rw [hc₀]; exact h0)]
    exact cls_congr0 _ j _ _ _ _ hc₀.symm
  have eX : (LinearEquiv.ofBijective ((φ q U a).mapH j) (P.mapH_bij (φ q U a) (fun n => tH_bij q U a (t q U a) (fun m n i θ x => htr q U a m n i θ x) n) j)).symm
      ((formCos q U.U a).cx.cls _ h1) = (cechH (Fk q U a) (Vk q U a) a).cx.cls c₁ h1' := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, P.mapH_cls (φ q U a) j c₁ h1' (by rw [hc₁]; exact h1)]
    exact cls_congr0 _ j _ _ _ _ hc₁.symm
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply, eY, eX]
  exact key

end CrystallineSemistableComparison.Om.GlobPf2
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.FinalC

section

@[expose] public section

open CategoryTheory AlgebraicGeometry GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.Nt2F

open CrystallineSemistableComparison.Om.Glob CrystallineSemistableComparison.Om.Cech CrystallineSemistableComparison.Om.Nt2

theorem glob_iso_c : type_of% (@CrystallineSemistableComparison.Om.Glob.glob_iso _) := CrystallineSemistableComparison.Om.GlobPf2.glob_iso
theorem cechOm_pull_c : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOm_pull _) := CrystallineSemistableComparison.Om.Cech.CechFormPull.cechOm_pull_pf

theorem hodge_iso_natural_cech : type_of% (@CrystallineSemistableComparison.Om.hdg_iso _) :=
  hdg_iso_of_ing glob_iso_c formToCO_bijective_i formToCO_smul_i cechOmAdd_smul_i cechOm_pull_c formCoch_pull_i
    cov_refine pullH_id pullC_id

end CrystallineSemistableComparison.Om.Nt2F
end
end
