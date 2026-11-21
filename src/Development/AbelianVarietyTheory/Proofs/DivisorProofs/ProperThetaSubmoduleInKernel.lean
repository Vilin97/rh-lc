module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaKerMaxInf

section Local

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def mkA (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : AF F := (a, b)

theorem tens_mem_schA_of_ne {f : SInf F κ} (hf : f ≠ 0) {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) (hs : tens (evI F) f r ∈ schA F κ) (f' : SInf F κ) :
    tens (evI F) f' r ∈ schA F κ := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (DFunLike.ext _ _ fun y => by rw [h y]; rfl)
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let pt : (κ → FiniteAdeleRing (𝓞 F) F) → κ → AF F := fun y i => mkA (e.symm (y₀ i)) (y i)
  let L := LinearMap.funLeft ℂ ℂ pt
  have hL : schA F κ ≤ (SB (κ → FiniteAdeleRing (𝓞 F) F)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f₀, g, hg, rfl⟩
    have : L (pureA F f₀ g) = f₀ y₀ • g := by
      funext y
      show f₀ (fun i => e (e.symm (y₀ i))) * g (fun i => y i) = f₀ y₀ * g y
      simp
    show L (pureA F f₀ g) ∈ SB _
    rw [this]
    exact Submodule.smul_mem _ _ hg
  have hLs : L (tens (evI F) f r) ∈ SB _ := hL hs
  refine Submodule.subset_span ⟨f', (f y₀)⁻¹ • L (tens (evI F) f r), Submodule.smul_mem _ _ hLs, ?_⟩
  funext x
  have hz : At (evI F) (fun i => mkA ((x i).1 - e.symm (y₀ i)) 0) := by
    intro u hu
    funext i
    have hu1 : u.1 = 0 := by
      have : e u.1 = 0 := hu
      simpa using this
    show mkA (u.1 * ((x i).1 - e.symm (y₀ i))) (u.2 * 0) = 0
    rw [hu1, zero_mul, mul_zero]
    rfl
  have hx : pt (fun i => (x i).2) + (fun i => mkA ((x i).1 - e.symm (y₀ i)) 0) = x := by
    funext i
    show mkA (e.symm (y₀ i) + ((x i).1 - e.symm (y₀ i))) ((x i).2 + 0) = x i
    rw [add_sub_cancel, add_zero]
    rfl
  have hrx : r x = r (pt fun i => (x i).2) := by
    have := hr (pt fun i => (x i).2) _ hz
    rw [hx] at this
    exact this
  have hev : (fun i => evI F (pt (fun i => (x i).2) i)) = y₀ := by
    funext i
    change e (e.symm (y₀ i)) = y₀ i
    exact e.apply_symm_apply _
  simp only [tens, pureA, Pi.smul_apply, smul_eq_mul, L, LinearMap.funLeft_apply, Function.comp_def]
  rw [hev, hrx]
  simp only [evI]
  field_simp

theorem rest_of_sub {f g : SInf F κ} (hfg : f - g ≠ 0) {r : (κ → AF F) → ℂ} (hr : Rest (evI F) (⇑(f - g)) r) :
    Rest (evI F) f r ∧ Rest (evI F) g r :=
  ⟨⟨hr.1, tens_mem_schA_of_ne hfg hr.1 hr.2 f⟩, ⟨hr.1, tens_mem_schA_of_ne hfg hr.1 hr.2 g⟩⟩

theorem tens_sub (f g : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(f - g)) r = tens (evI F) f r - tens (evI F) g r := by
  funext x
  simp [tens, sub_mul]

theorem actsD_sub (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) {f g f₁ g₁ : SInf F κ} (hfg : f - g ≠ 0)
    (hf : ActsD (evI F) (fun t => T t) f f₁) (hg : ActsD (evI F) (fun t => T t) g g₁) :
    ActsD (evI F) (fun t => T t) (⇑(f - g)) (⇑(f₁ - g₁)) := by
  intro r hr x
  obtain ⟨hrf, hrg⟩ := rest_of_sub hfg hr
  have h := (hf r hrf x).sub (hg r hrg x)
  rw [tens_sub, tens_sub]
  have e1 : (fun t => T t (tens (evI F) f r - tens (evI F) g r) x) =
      fun t => T t (tens (evI F) f r) x - T t (tens (evI F) g r) x := by
    funext t
    simp [map_sub]
  show HasDerivAt (fun t => T t (tens (evI F) f r - tens (evI F) g r) x) (tens (evI F) f₁ r x - tens (evI F) g₁ r x) 0
  rw [e1]
  exact h

theorem acts_sub (T : Module.End ℂ ((κ → AF F) → ℂ)) {f g f₁ g₁ : SInf F κ} (hfg : f - g ≠ 0)
    (hf : Acts (evI F) T f f₁) (hg : Acts (evI F) T g g₁) :
    Acts (evI F) T (⇑(f - g)) (⇑(f₁ - g₁)) := by
  intro r hr
  obtain ⟨hrf, hrg⟩ := rest_of_sub hfg hr
  rw [tens_sub, tens_sub, map_sub, hf r hrf, hg r hrg]

end Local

end GlobalTheory.ThetaKerMaxInf
