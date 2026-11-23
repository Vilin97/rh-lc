module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteDimensionalSpan
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGoodStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → IsCoefRing σ emb O → Submodule.IsFullLattice D.host.E M → (harmLat σ emb O m w B M).FG ∧ Submodule.span ℂ (harmLat σ emb O m w B M : Set (PolF D m n)) = harm m w B := by
  intro D m n w B K _ _ σ emb O M hw hm hc hM
  letI := hM
  exact GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span D m n w B K σ emb O M hw hm hc
    (by infer_instance)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MtLatFgOfReps

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links




attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie

theorem fg_of_eval {R G W I : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup W] [Module R W] [Finite I]
    (L : Submodule R (G → W)) (y : I → G) (C : I → Submodule R W) (hC : ∀ c, (C c).FG)
    (hmem : ∀ f ∈ L, ∀ c, f (y c) ∈ C c) (hinj : ∀ f ∈ L, (∀ c, f (y c) = 0) → f = 0) : L.FG := by
  haveI : ∀ c, IsNoetherian R (C c) := fun c => isNoetherian_of_fg_of_noetherian _ (hC c)
  let ev : L →ₗ[R] ∀ c, C c :=
    { toFun := fun f c => ⟨f.1 (y c), hmem f.1 f.2 c⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun f hf => ?_
    exact Subtype.ext (hinj f.1 f.2 fun c => congrArg Subtype.val (congrFun hf c))
  haveI : IsNoetherian R L := isNoetherian_of_injective ev hev
  exact Module.Finite.iff_fg.1 inferInstance

section Eval

variable {D : D7} {S T : HSp D} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
  {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ}

theorem eq_zero_of_reps (B : Base S T) (t : Twist D Circle) {I : Type} {y : I → Bridge.Gf S}
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) {f : Bridge.Gf S → PolF D T.rank S.rank} (hf : f ∈ B.formsC t)
    (h0 : ∀ c, f (y c) = 0) : f = 0 := by
  have hlaw : B.HasLaw t f := ((B.mem_formsC).1 hf).2
  funext h
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := hy h
  have h1 := hlaw γ (y c) k
  rw [h0 c, map_zero, smul_zero, ← e] at h1
  exact h1

theorem mtLat_fg_of_reps [IsNoetherianRing O] (B : Base S T) (t : Twist D Circle) {I : Type} [Finite I] {y : I → Bridge.Gf S}
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) (hfg : ∀ c, (B.coefLat σ emb O (y c)).FG) :
    (B.mtLat σ emb O t).FG :=
  fg_of_eval _ y (fun c => B.coefLat σ emb O (y c)) hfg (fun _ hf c => ((B.mem_mtLat σ emb O).1 hf).2 (y c))
    fun _ hf h0 => eq_zero_of_reps B t hy ((B.mem_mtLat σ emb O).1 hf).1 h0

end Eval

theorem latFG_of_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ρ.LatFG := by
  intro D N X ρ hρ i j b k Q ψ hT
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good D N X ρ hρ i j b k Q ψ hT
  have hc := hρ.classes i j b _ hg ha
  haveI : IsNoetherianRing (ρ.eOk i b k).range :=
    isNoetherianRing_of_surjective (X.Ok i k) _ (ρ.eOk i b k).rangeRestrict (ρ.eOk i b k).rangeRestrict_surjective
  have hB := hρ.base i j b
  refine mtLat_fg_of_reps _ _ hc.reps fun c => ?_
  refine (GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space D _ _ _ _ _ _ _ _ _ hB.wt (fun τ => ?_) (hρ.isCoefRing_k i b k) ?_).1
  · have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  · classical
    have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
        IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
      intro V Λ hΛ
      haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
      refine ⟨?_⟩
      obtain ⟨s, hs⟩ := hΛ.1.fg
      apply eq_top_iff.mpr
      intro y _
      let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
        ∑ i, ∑ j, star (x i) * V.gram i j * y j
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
      have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
        exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
      let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
        carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
        zero_mem' := by refine ⟨0, ?_⟩; simp [f]
        add_mem' := by
          rintro x z ⟨b, hb⟩ ⟨c, hc⟩
          refine ⟨b + c, ?_⟩
          change (b : D.host.E) + c = _
          rw [hb, hc]
          simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
        smul_mem' := by
          rintro c x ⟨b, hb⟩
          refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
          simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          change star (c : D.host.E) * _ = _
          ring }
      have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
        intro x hx
        obtain ⟨b, hb⟩ := ha x hx
        exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
      have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
        apply (hΛ.2 _).2
        intro x hx
        have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
        obtain ⟨b, hb⟩ := hxP
        refine ⟨b, ?_⟩
        rw [hb]
        dsimp only [f, Pi.smul_apply]
        simp only [smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
        Submodule.subset_span hy
      have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
        (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
      change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
        ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
      rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
      exact this
    haveI : Submodule.IsFullLattice D.host.E (ρ.B i j b).F.ΛS := hfull _ _ hB.frame.sdS
    haveI : Submodule.IsFullLattice D.host.E
        ((ρ.B i j b).latAt (finPt (Vc D j) (ρ.rep i j b (ρ.tw i b k Q ψ) c))) :=
      Formalism.UG.P.csGlob_lattice (F := D.host.F) (ρ.B i j b).F.ΛS (Module.Finite.iff_fg.2 hB.frame.sdS.1.fg)
        (Submodule.IsFullLattice.span_eq_top (A := D.host.E) (M := (ρ.B i j b).F.ΛS)) _
    infer_instance

end GlobalTheory.SeriesTie

end
end
end
