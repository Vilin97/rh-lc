module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Mathlib.LinearAlgebra.Eigenspace.Basic
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaModel

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.InflAct

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.inflAct :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] [Normal k E] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (τ : E ≃+* E) (σ : G k Ω), IsLift τ σ.toRingEquiv →
      ∀ x y, Infl k D e x y → Infl k D e (galoisActionOnCohomology D e τ x) (conjRep (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) σ y) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ D e τ σ h x y hxy
  obtain ⟨z, z', rfl, rfl, hz⟩ := hxy
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) σ z'
  refine ⟨z₁, z₂, by rw [galois_action_cohomology_eq_conj D e h, e₁], by rw [conjRep_apply, e₂], fun g => ?_⟩
  have hc : conjHom (galOf k E Ω) σ ⟨galEmb k E Ω g, galEmb_mem k E Ω g⟩ =
      ⟨galEmb k E Ω (conjGal h g), galEmb_mem k E Ω _⟩ := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  rw [f₂, f₁, conjGS_toGS, hc, hz]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.InflUnique

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base


theorem UpperTheory.V.Base.inflUnique :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      (∀ x, ∃ y, Infl k D e x y) ∧ ∀ x x' y y', Infl k D e x y → Infl k D e x' y' → (x = x' ↔ y = y') := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨hemb, -, -⟩ := galEmbTop k E Ω
  let ψ : G E Ω →* galOf k E Ω := (galEmb k E Ω).codRestrict _ (galEmb_mem k E Ω)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨τ, hτ⟩
    refine ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => hτ x), ?_⟩
    apply Subtype.ext
    ext x
    rfl
  let Ψ : G E Ω ≃* galOf k E Ω :=
    MulEquiv.ofBijective ψ ⟨fun a b h => hemb.injective (congrArg Subtype.val h), hsurj⟩
  have hΨ : ∀ σ, Ψ σ = ⟨galEmb k E Ω σ, galEmb_mem k E Ω σ⟩ := fun _ => rfl
  have hcont : Continuous (fun u : galOf k E Ω => Ψ.symm u) := by
    rw [hemb.continuous_iff]
    have hc : (galEmb k E Ω) ∘ (fun u : galOf k E Ω => Ψ.symm u) = Subtype.val := by
      funext u
      show ((Ψ (Ψ.symm u) : galOf k E Ω) : G k Ω) = u
      rw [Ψ.apply_symm_apply]
    rw [hc]
    exact continuous_subtype_val
  have hEk : ∀ σ : G E Ω, LDataCardLeFinrank.qzG k Ω l e (galEmb k E Ω σ) = LDataCardLeFinrank.qzG E Ω l e σ := by
    intro σ
    have hχ : (cycZ k Ω l ^ (-e)).comp (galEmb k E Ω) = cycZ E Ω l ^ (-e) := by
      refine MonoidHom.ext fun τ => ?_
      rw [MonoidHom.comp_apply]
      simp only [MonoidHom.zpow_apply]
      rfl
    show scalRep (QZ l) (cycZ k Ω l ^ (-e)) (galEmb k E Ω σ) = scalRep (QZ l) (cycZ E Ω l ^ (-e)) σ
    rw [← hχ]
    rfl
  have hrep : ∀ σ : G E Ω, LDataCardLeFinrank.qzG k Ω l e (galEmb k E Ω σ) = qzTw D e (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) σ) := by
    intro σ
    have h := DFunLike.congr_fun (LDataCardLeFinrank.qzTw_comp_toGS D e) σ
    rw [MonoidHom.comp_apply] at h
    rw [hEk]
    exact h.symm
  have hu : ∀ u : galOf k E Ω, (u : G k Ω) = galEmb k E Ω (Ψ.symm u) := by
    intro u
    conv_lhs => rw [← Ψ.apply_symm_apply u]
    rfl
  have hTs : Function.Surjective (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) :=
    QuotientGroup.mk'_surjective _
  constructor
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    let f : galOf k E Ω → QZ l := fun u => (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm u))
    have hf : f ∈ Z1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) := by
      refine ⟨z.2.1.comp ((continuous_toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))).comp hcont), ?_⟩
      intro u v
      show (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm (u * v))) =
        (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm u)) +
          ((LDataCardLeFinrank.qzG k Ω l e).comp (galOf k E Ω).subtype u) ((z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm v)))
      rw [map_mul, map_mul, z.2.2, MonoidHom.comp_apply, Subgroup.coe_subtype, hu u, hrep]
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, z, ⟨f, hf⟩, rfl, rfl, ?_⟩
    intro σ
    show (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm ⟨galEmb k E Ω σ, _⟩)) = _
    rw [← hΨ, Ψ.symm_apply_apply]
  · rintro x x' y y' ⟨z1, w1, rfl, rfl, h1⟩ ⟨z2, w2, rfl, rfl, h2⟩
    rw [mk_eq_mk, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    apply exists_congr
    intro m
    constructor
    · intro h u
      obtain ⟨σ, rfl⟩ := Ψ.surjective u
      have h3 := h (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) σ)
      rw [Submodule.coe_sub, Pi.sub_apply] at h3
      rw [hΨ, h1, h2, h3]
      exact congrArg (fun T => T m - m) (hrep σ).symm
    · intro h g
      obtain ⟨σ, rfl⟩ := hTs g
      have h3 := h (Ψ σ)
      rw [hΨ, h1, h2] at h3
      rw [Submodule.coe_sub, Pi.sub_apply, h3]
      exact congrArg (fun T => T m - m) (hrep σ)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaLenEq

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base


theorem UpperTheory.V.Base.shaLenEq :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      shaLen D e = Module.length ℤ_[l] (ShaU (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω)) ∧
      ∀ [Normal k E] (τ : E ≃+* E) (σ : G k Ω), IsLift τ σ.toRingEquiv → ∀ s : ℤ_[l],
        Module.length ℤ_[l] ↥(Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s) =
          Module.length ℤ_[l] (Module.End.eigenspace (shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ) s) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨Φ, hΦ⟩ := shaModel k E Ω l D e
  refine ⟨Φ.length_eq, ?_⟩
  intro _ τ σ hτσ s
  have key : ∀ x : ↥(Sha D e), ∃ h : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e,
      Φ ⟨_, h⟩ = shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ (Φ x) := by
    intro x
    set y := shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ (Φ x) with hy
    have h1 : Infl k D e (galoisActionOnCohomology D e τ (x : H1 (qzTw D e))) (y : H1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω)) :=
      inflAct k E Ω l D e τ σ hτσ _ _ (hΦ x)
    have h2 := hΦ (Φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at h2
    have heq : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) = ((Φ.symm y : ↥(Sha D e)) : H1 (qzTw D e)) :=
      ((inflUnique k E Ω l D e).2 _ _ _ _ h1 h2).2 rfl
    have hmem : galoisActionOnCohomology D e τ (x : H1 (qzTw D e)) ∈ Sha D e := by
      rw [heq]
      exact (Φ.symm y).2
    refine ⟨hmem, ?_⟩
    have hsub : (⟨_, hmem⟩ : ↥(Sha D e)) = Φ.symm y := Subtype.ext heq
    rw [hsub, LinearEquiv.apply_symm_apply]
  have hle : Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s ≤ Sha D e := inf_le_left
  have hmap : Submodule.map (Φ : ↥(Sha D e) →ₗ[ℤ_[l]] ↥(ShaU (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω)))
      (Submodule.comap (Sha D e).subtype (Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s)) =
      Module.End.eigenspace (shaRep (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω) σ) s := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext y
    obtain ⟨h, hk⟩ := key (Φ.symm y)
    rw [LinearEquiv.apply_symm_apply] at hk
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    refine ⟨fun hx => ?_, fun hx => ⟨(Φ.symm y).2, ?_⟩⟩
    · have hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y := Subtype.ext hx.2
      refine hk.symm.trans ?_
      rw [hs, Φ.map_smul, LinearEquiv.apply_symm_apply]
    · have hs : (⟨_, h⟩ : ↥(Sha D e)) = s • Φ.symm y := by
        apply Φ.injective
        refine hk.trans (hx.trans ?_)
        rw [Φ.map_smul, LinearEquiv.apply_symm_apply]
      exact congrArg Subtype.val hs
  rw [← hmap]
  exact ((Submodule.comapSubtypeEquivOfLe hle).symm.trans (Φ.submoduleMap _)).length_eq
end
end
