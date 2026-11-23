module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabiliserBijectiveOfFinite
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.LatSOfMem
public import Formalism.SatakeDualWeyl.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.DualLStable
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.PrVTensInt

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.InclEMemTensInt

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct

section Decomp

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

def TQ {m : ℕ} (b : Fin m → 𝓞 E) (s : E ⊗[F] R) : Prop :=
  ∃ r : Fin m → R, (∀ j, r j ∈ S₂) ∧ s = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j

variable {R S₂}

theorem tq_zero {m : ℕ} (b : Fin m → 𝓞 E) : TQ (F := F) R S₂ b 0 :=
  ⟨0, fun _ => S₂.zero_mem, by simp⟩

theorem tq_add {m : ℕ} (b : Fin m → 𝓞 E) {x y : E ⊗[F] R} (hx : TQ R S₂ b x) (hy : TQ R S₂ b y) :
    TQ R S₂ b (x + y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  exact ⟨r + r', fun j => S₂.add_mem (hr j) (hr' j), by
    simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem tq_neg {m : ℕ} (b : Fin m → 𝓞 E) {x : E ⊗[F] R} (hx : TQ R S₂ b x) : TQ R S₂ b (-x) := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact ⟨-r, fun j => S₂.neg_mem (hr j), by simp [TensorProduct.tmul_neg]⟩

theorem tq_sum {m : ℕ} (b : Fin m → 𝓞 E) {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] R)
    (h : ∀ i ∈ s, TQ R S₂ b (f i)) : TQ R S₂ b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (TQ R S₂ b) (fun _ _ hx hy => tq_add b hx hy) (tq_zero b) h

theorem tq_tmul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (e : 𝓞 E) {y : R} (hy : y ∈ S₂) : TQ R S₂ b (algebraMap (𝓞 E) E e ⊗ₜ[F] y) := by
  have he : e ∈ Submodule.span ℤ (Set.range b) := by rw [hb]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 he
  refine ⟨fun j => c j • y, fun j => zsmul_mem hy (c j), ?_⟩

  rw [← hc, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  exact TensorProduct.smul_tmul _ _ _

theorem tq_mul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {x y : E ⊗[F] R} (hx : TQ R S₂ b x) (hy : TQ R S₂ b y) : TQ R S₂ b (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine tq_sum b _ _ fun j _ => tq_sum b _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
  exact tq_tmul b hb _ (S₂.mul_mem (hr j) (hr' k))

theorem tq_decomp {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) S₂) : TQ R S₂ b s := by
  unfold tensInt at hs
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, ⟨e, rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact tq_tmul b hb e S₂.one_mem
    · have h1 := tq_tmul (F := F) b hb (1 : 𝓞 E) hy
      simpa using h1
  | zero => exact tq_zero b
  | one =>
    have h1 := tq_tmul (F := F) b hb (1 : 𝓞 E) (S₂.one_mem)
    simpa [Algebra.TensorProduct.one_def] using h1
  | add x y _ _ hx hy => exact tq_add b hx hy
  | neg x _ hx => exact tq_neg b hx
  | mul x y _ _ hx hy => exact tq_mul b hb hx hy

theorem tensInt_tmul_mem (e : 𝓞 E) {y : R} (hy : y ∈ S₂) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] y ∈ tensInt (F := F) R (intOE E) S₂ := by
  have h1 : algebraMap (𝓞 E) E e ⊗ₜ[F] (1 : R) ∈ tensInt (F := F) R (intOE E) S₂ :=
    Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩)
  have h2 : (1 : E) ⊗ₜ[F] y ∈ tensInt (F := F) R (intOE E) S₂ :=
    Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have h3 := Subring.mul_mem _ h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3

theorem inclE_mem_tensInt (e : 𝓞 E) :
    inclE (F := F) R (algebraMap (𝓞 E) E e) ∈ tensInt (F := F) R (intOE E) S₂ :=
  tensInt_tmul_mem e S₂.one_mem

end Decomp

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.AdelicLocalLattice

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct

section Lat

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
variable (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

theorem latS_decomp {m k : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (g : Fin k → (Fin n → E))
    (hg : Submodule.span (𝓞 E) (Set.range g) = Λ) (y : Fin n → E ⊗[F] R)
    (hy : y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ) :
    ∃ r : Fin k → Fin m → R, (∀ i j, r i j ∈ S₂) ∧ ∀ l, y l =
      ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r i j) * inclE (F := F) R (g i l) := by
  set S := tensInt (F := F) R (intOE E) S₂
  set G : Fin k → (Fin n → E ⊗[F] R) := fun i l => inclE (F := F) R (g i l)
  have hle : latS (F := F) R S Λ ≤ Submodule.span S (Set.range G) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← hg] at hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hx
    have : (fun l => inclE (F := F) R ((∑ i, a i • g i) l)) =
        ∑ i, (⟨inclE (F := F) R (algebraMap (𝓞 E) E (a i)), inclE_mem_tensInt (F := F) (R := R) (S₂ := S₂) (a i)⟩ : S) • G i := by
      funext l

      rw [Finset.sum_apply, Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
    show (fun l => inclE (F := F) R ((∑ i, a i • g i) l)) ∈ Submodule.span S (Set.range G)
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 (hle hy)
  choose r hr hsr using fun i => tq_decomp (F := F) (R := R) (S₂ := S₂) b hb (s i).2
  refine ⟨r, hr, fun l => ?_⟩
  rw [← hs, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, hsr i, Finset.sum_mul]

end Lat

section Glue

variable {F : Type} [Field F] [NumberField F]

def glueInt (r : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hr : ∀ v, r v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨r, Filter.Eventually.of_forall hr⟩

theorem glueInt_apply (r : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hr : ∀ v, r v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    glueInt r hr v = r v := rfl

theorem glueInt_mem (r : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hr : ∀ v, r v ∈ v.adicCompletionIntegers F) : glueInt r hr ∈ intAd F := by
  first
  | exact fun v => hr v
  | (intro v; simpa [glueInt_apply] using hr v)
  | (simp only [intAd]; intro v; exact hr v)
  | simp [intAd, glueInt_apply, hr]
  | (unfold intAd; guard_target =ₛ True)

end Glue

theorem adelic_local_lattice : AdLocLat := by
  intro F E _ _ _ _ _ n Λ hΛ x hx
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (Module.Finite.iff_fg.1 hΛ)
  choose r hr hxr using fun v : HeightOneSpectrum (𝓞 F) =>
    latS_decomp (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring b hb Λ g hg _ (hx v)
  set Rg : Fin k → Fin m → FiniteAdeleRing (𝓞 F) F :=
    fun i j => glueInt (fun v => r v i j) (fun v => hr v i j) with hRg
  have hx' : x = fun l => ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j) *
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l) := by
    funext l
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_
    rw [map_sub, sub_eq_zero]
    refine (hxr v l).trans ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    rfl
  have hgΛ : ∀ i, g i ∈ Λ := fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩
  have hmem : ∀ i j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := fun i j =>
    tensInt_tmul_mem (b j) (glueInt_mem _ _)
  have hsum : (fun l => ∑ i, ∑ j, (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] Rg i j) *
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l)) =
      ∑ i, ∑ j, (⟨_, hmem i j⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) •
        (fun l => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (g i l)) := by
    funext l
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
  rw [hx', hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨g i, hgΛ i, rfl⟩)

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapPropertiesOfSymmetricForms

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def DualLoc (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls D.R.m) (z : Fin (D.R.N D.R.m) → D.host.E), z ∈ Ld D u D.R.m le_rfl c →
    ((bc (prV (E := D.host.E) (Tf.atT.eV v).1) ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (z a)) ∈
      latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
          (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb))

def FvStab (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
    γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
    ∀ (v : (D.mem u).A.vT) (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c)))
      (hx : γ.1.1 *ᵥ x.1 ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)),
      (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ ⟨γ.1.1 *ᵥ x.1, hx⟩) =
        (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ x)

theorem stabLF_of_fv (Tf : FormsTiedSym D u Ch chOf) (hF : FvStab Tf) : StabLF Tf :=
  stabLF_of Tf (fun c γ hγ => ⟨stab_lat Tf latLocGlob adelic_local_lattice c γ hγ, hF c γ hγ⟩)

theorem stabiliser_bijective_self_dual
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hF : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      FvStab Tf) : StabiliserMapBijective :=
  stabiliser_bijective_of_finite hSD (fun D u Ch chOf Tf => stabLF_of_fv Tf (hF D u Ch chOf Tf))

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end
