module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DualKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LenDual
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.IdealNormClassCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LayerGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LayerUniq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ShaDGen
public import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CokerDual

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.cokerDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (g : Module.End ℤ_[l] M) (t : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l)), (∀ x φ, t x φ = x (g φ)) →
        cokerLen t = Module.length ℤ_[l] (LinearMap.ker g) := by
  intro l _ M _ _ g t h
  have ht : t = LinearMap.lcomp ℤ_[l] (QZ l) g := LinearMap.ext fun x => LinearMap.ext fun φ => h x φ
  obtain ⟨h1, h2⟩ := UpperTheory.V.Tower.dualKer l M M g
  have hr : LinearMap.range t
      = LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (LinearMap.ker g).subtype) := by
    rw [ht]; exact h1
  rw [← UpperTheory.V.Tower.lenDual l (LinearMap.ker g)]
  exact ((Submodule.quotEquivOfEq _ _ hr).trans
    (LinearMap.quotKerEquivOfSurjective _ (h2 (LinearMap.ker g)))).length_eq
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsGen

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.existsGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → (l ≠ 2 ∨ U ≤ gamU l ⊤) → ∃ γ, IsGen l U γ := by
  intro k Ω _ _ _ _ _ l _ U hU hcond
  have hclosed : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hU.isCompact.image (continuous_cycZ k Ω l)).isClosed
  have hc : l ≠ 2 ∨ U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l 2 := by
    by_cases hl : l = 2
    · rcases hcond with h | h
      · exact absurd hl h
      · right
        rw [Subgroup.map_le_iff_le_comap]
        intro x hx
        have hx' := h hx
        simp only [gamU, levU, qExp, if_pos hl, Subgroup.mem_inf] at hx'
        exact hx'.2
    · exact Or.inl hl
  obtain ⟨γ', hγ', hle⟩ := UpperTheory.V.Kum.existsGen l (U.map (cycZ k Ω l)) hclosed hc
  obtain ⟨γ, hγU, rfl⟩ := Subgroup.mem_map.mp hγ'
  exact ⟨γ, hγU, hle⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.GenGal

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.genGal :
    ∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], IsClosed (galOf k L Ω : Set (G k Ω)) ∧ (Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤) ∧
        (Procyc L Ω l → ∃ γ, IsGen l (galOf k L Ω) γ) := by
  intro k L Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hcl : IsClosed (galOf k L Ω : Set (G k Ω)) :=
    Subgroup.isClosed_of_isOpen _ (galEmbTop k L Ω).2.1
  have hχ : ∀ g : G L Ω, cycZ k Ω l (galEmb k L Ω g) = cycZ L Ω l g := fun g =>
    DFunLike.congr_fun (galEmbFam k L Ω l).2.2.1 g
  have hiff : Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤ := by
    by_cases h : l = 2
    · subst h
      refine or_congr_right ?_
      rw [← range_galEmb]
      constructor
      · rintro h _ ⟨g, rfl⟩
        refine ⟨trivial, ?_⟩
        show cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2
        rw [hχ]
        exact h g
      · intro h g
        have h' : cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2 := (h ⟨g, rfl⟩).2
        rw [hχ] at h'
        exact h'
    · exact ⟨fun _ => Or.inl h, fun _ => Or.inl h⟩
  exact ⟨hcl, hiff, fun h => UpperTheory.V.Tower.existsGen k Ω l _ hcl (hiff.1 h)⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.Imports

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.desc :
    ∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (D : LData L Ω l) (e : ℤ) (U : Subgroup (G k Ω)) [U.Normal], e ≠ 0 → Procyc L Ω l → cycU l U = cycU l (galOf k L Ω) →
        ∃ Φ : Sha D e ≃ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e, IsDesc L D e U Φ.toLinearMap := by
  intro k L Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e U _ he hpro hcyc
  have hfam := galEmbFam k L Ω l
  have hcycE : ∀ h : G L Ω, cycZ k Ω l (galEmb k L Ω h) = cycZ L Ω l h := fun h => by
    rw [← MonoidHom.comp_apply, hfam.2.2.1]
  have hlift : ∀ σ ∈ galOf k L Ω, ∃ h : G L Ω, galEmb k L Ω h = σ := by
    intro σ hσ
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ, by ext x; rfl⟩
  have hmap : Subgroup.map (galEmb k L Ω) (cycU l (⊤ : Subgroup (G L Ω))) = cycU l U := by
    rw [hcyc]
    ext σ
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · intro x
        exact g.commutes x
      · rw [MonoidHom.mem_ker, hcycE]
        exact (Subgroup.mem_inf.1 hg).2
    · intro hσ
      obtain ⟨hσG, hσK⟩ := Subgroup.mem_inf.1 hσ
      obtain ⟨h, rfl⟩ := hlift σ hσG
      refine ⟨h, Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker, ← hcycE]
      exact hσK
  obtain ⟨Ψ, hΨ⟩ := dinfTransport k Ω L Ω (algebraMap k L) (RingEquiv.refl Ω)
    (fun x => IsScalarTower.algebraMap_apply k L Ω x) (galEmb k L Ω) (fun g x => rfl)
    l l U ⊤ hmap
  have hdTw : ∀ (g : G k Ω) (χ : Dinf l l U) (w : cycU l U),
      ((dTw l l U e g χ : Dinf l l U) : cycU l U → QZ l) w =
        (((cycZ k Ω l ^ (-e)) g : ℤ_[l]ˣ) : ℤ_[l]) • (χ : cycU l U → QZ l) (conjHom (cycU l U) g w) := by
    intro g χ w
    rfl
  have hq : ∀ (h : G L Ω) (m : QZ l),
      qzG L Ω l e h m = (((cycZ L Ω l ^ (-e)) h : ℤ_[l]ˣ) : ℤ_[l]) • m := fun h m => rfl
  have hqE : ∀ (h : G L Ω) (m : QZ l),
      (((cycZ k Ω l ^ (-e)) (galEmb k L Ω h) : ℤ_[l]ˣ) : ℤ_[l]) • m = qzG L Ω l e h m := by
    intro h m
    rw [← hfam.2.2.2 e]
    rfl
  have hmemE : ∀ u : cycU l (⊤ : Subgroup (G L Ω)), galEmb k L Ω u ∈ cycU l U := fun u =>
    hmap ▸ Subgroup.mem_map_of_mem _ u.2
  let E : cycU l (⊤ : Subgroup (G L Ω)) → cycU l U := fun u => ⟨galEmb k L Ω u, hmemE u⟩
  have hEsurj : ∀ w : cycU l U, ∃ u, E u = w := by
    intro w
    have hw : (w : G k Ω) ∈ Subgroup.map (galEmb k L Ω) (cycU l (⊤ : Subgroup (G L Ω))) := by
      rw [hmap]
      exact w.2
    obtain ⟨u, hu, huw⟩ := hw
    exact ⟨⟨u, hu⟩, Subtype.ext huw⟩
  have key : ∀ χ : Dinf l l U, χ ∈ ShaD l l U (galOf k L Ω) e ↔
      ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) : cycU l (⊤ : Subgroup (G L Ω)) → QZ l) ∈
        EqHom l (Uinf L Ω l) (qzG L Ω l e) := by
    intro χ
    have hX : ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) : cycU l (⊤ : Subgroup (G L Ω)) → QZ l) ∈
        XDual l (Uinf L Ω l) ℤ_[l] (QZ l) := (Ψ χ).2
    have hΨE : ∀ u, ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) :
        cycU l (⊤ : Subgroup (G L Ω)) → QZ l) u = (χ : cycU l U → QZ l) (E u) :=
      fun u => hΨ χ u (E u) rfl
    constructor
    · intro hinv
      refine Submodule.mem_inf.2 ⟨hX, (Submodule.mem_iInf _).2 fun h => ?_⟩
      intro u u' huu
      rw [hΨE, hΨE]
      have hg : galEmb k L Ω h ∈ galOf k L Ω := fun x => h.commutes x
      have hinvg := (Representation.mem_invariants _ _).1 hinv ⟨_, hg⟩
      have h2 : ((dTw l l U e (galEmb k L Ω h) χ : Dinf l l U) : cycU l U → QZ l) (E u') =
          (χ : cycU l U → QZ l) (E u') :=
        congrArg (fun y : Dinf l l U => (y : cycU l U → QZ l) (E u')) hinvg
      rw [hdTw] at h2
      have hconj : conjHom (cycU l U) (galEmb k L Ω h) (E u') = E u := by
        apply Subtype.ext
        show (galEmb k L Ω h)⁻¹ * galEmb k L Ω u' * galEmb k L Ω h = galEmb k L Ω u
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        ext x
        show h⁻¹ ((u' : G L Ω) (h x)) = (u : G L Ω) x
        rw [show (u' : G L Ω) (h x) = h ((u : G L Ω) x) from huu x, AlgEquiv.aut_inv,
          AlgEquiv.symm_apply_apply]
      rw [hconj, hqE] at h2
      exact h2.symm
    · intro hE
      obtain ⟨_, hC⟩ := Submodule.mem_inf.1 hE
      rw [Submodule.mem_iInf] at hC
      refine (Representation.mem_invariants _ _).2 fun g => ?_
      obtain ⟨h, hh⟩ := hlift g g.2
      apply Subtype.ext
      funext w
      show ((dTw l l U e (g : G k Ω) χ : Dinf l l U) : cycU l U → QZ l) w = (χ : cycU l U → QZ l) w
      rw [hdTw]
      obtain ⟨u', rfl⟩ := hEsurj w
      have hu : h⁻¹ * (u' : G L Ω) * h ∈ cycU l (⊤ : Subgroup (G L Ω)) := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
          MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 u'.2).2, mul_one, inv_mul_cancel]
      have hcond := hC h ⟨_, hu⟩ u' (fun x => by
        show (u' : G L Ω) (h x) = h ((h⁻¹ * (u' : G L Ω) * h) x)
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply])
      rw [hΨE, hΨE] at hcond
      have hconj : conjHom (cycU l U) (g : G k Ω) (E u') = E ⟨_, hu⟩ := by
        apply Subtype.ext
        show (g : G k Ω)⁻¹ * galEmb k L Ω u' * (g : G k Ω) = galEmb k L Ω (h⁻¹ * (u' : G L Ω) * h)
        rw [← hh, map_mul, map_mul, map_inv]
      rw [hconj, ← hh, hqE]
      exact hcond.symm
  have hR : ∀ x : Sha D e, resInf D e (x : H1 (qzTw D e)) ∈ EqHom l (Uinf L Ω l) (qzG L Ω l e) := by
    intro x
    rw [← resInfOnto L Ω l D e he hpro]
    exact Submodule.mem_map_of_mem x.2
  have hED : ∀ f, f ∈ EqHom l (Uinf L Ω l) (qzG L Ω l e) → f ∈ Dinf l l (⊤ : Subgroup (G L Ω)) :=
    fun f hf => (Submodule.mem_inf.1 hf).1
  let R0 : Sha D e →ₗ[ℤ_[l]] Dinf l l (⊤ : Subgroup (G L Ω)) :=
    LinearMap.codRestrict _ ((resInf D e).comp (Sha D e).subtype) (fun x => hED _ (hR x))
  let f : Sha D e →ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e :=
    LinearMap.codRestrict _ (Ψ.symm.toLinearMap.comp R0) (fun x => (key _).2 (by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hR x))
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : Ψ.symm (R0 x) = Ψ.symm (R0 y) := congrArg Subtype.val hxy
    have h2 : R0 x = R0 y := Ψ.symm.injective h1
    have h3 : resInf D e x = resInf D e y := congrArg Subtype.val h2
    exact Subtype.ext (resInfInj L Ω l D e he hpro h3)
  have hfsurj : Function.Surjective f := by
    intro χ
    have hm := (key (χ : Dinf l l U)).1 χ.2
    rw [← resInfOnto L Ω l D e he hpro] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    show Ψ.symm (R0 ⟨x, hx⟩) = χ
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hxe
  refine ⟨LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩, ?_⟩
  intro x u u' hu
  show ((Ψ.symm (R0 x) : Dinf l l U) : cycU l U → QZ l) u' = resInf D e x u
  rw [← hΨ (Ψ.symm (R0 x)) u u' hu, LinearEquiv.apply_symm_apply]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsDescends

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

noncomputable section

namespace UpperTheory.V.Tower

section Step0

variable {l : ℕ} [Fact l.Prime] {L₀ : Type} [Field L₀] [NumberField L₀] {Ω : Type} [Field Ω] [Algebra L₀ Ω] [IsAlgClosure L₀ Ω]

theorem step0 (hμ : HasMuQ l L₀) {γ : G L₀ Ω} (hγ : IsGen l ⊤ γ) {e : ℤ} (he : e ≠ 0) (m : ℕ) (L₁ : Type) [Field L₁]
    [NumberField L₁] [Algebra L₀ L₁] (hL : IsLayer l m L₀ L₁) :
    shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ Ω)) e γ ^ l ^ m - 1) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L₀
  haveI : FiniteDimensional L₀ L₁ := Module.Finite.of_restrictScalars_finite ℚ L₀ L₁
  let j : L₁ →ₐ[L₀] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra L₁ Ω := j.toRingHom.toAlgebra
  haveI : IsScalarTower L₀ L₁ Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Algebra.IsAlgebraic L₀ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure L₁ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := L₀) L₁⟩
  obtain ⟨D⟩ := Formalism.GaloisCohomology.ldataExists L₁ Ω l
  have hμ₁ : HasMuQ l L₁ := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨_, hζ.map_of_injective (algebraMap L₀ L₁).injective⟩
  have hU := (layerUniq L₀ Ω l hμ).2.1 m L₁ hL
  obtain ⟨Φ, -⟩ := desc L₀ L₁ Ω l D e ⊤ he ((muQ L₁ Ω l).2.2.2.1 hμ₁).2 (by rw [hU, cycU_levU])
  have hg := ((layerGen L₀ Ω l hμ).2 γ hγ).2.2 m
  rw [← hU] at hg
  rw [← shaLen_eq_shaInv D, shaLen, Φ.length_eq, (shaDGen L₀ Ω l l ⊤ _ e _ isClosed_univ le_top hg).2, ← map_pow]
  exact (cokerDual l _ _ _ fun x φ => by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, xTw_apply_apply]; rfl).symm


variable (l L₀ Ω) in
theorem exists_descends (hμ : HasMuQ l L₀) : ∃ γ : G L₀ Ω, IsGen l ⊤ γ ∧
    PropA.IsLevel l (cycZ L₀ Ω l γ : ℤ_[l]ˣ) (cZero l L₀) ∧ (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ cZero l L₀)) ∧
    ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
      shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ Ω)) e γ ^ l ^ m - 1) := by
  obtain ⟨γ, hγ⟩ := (genGal L₀ L₀ Ω l).2.2 ((muQ L₀ Ω l).2.2.2.1 hμ).2
  rw [galOf_self] at hγ
  exact ⟨γ, hγ, ((layerGen L₀ Ω l hμ).2 γ hγ).1, ((muQ L₀ Ω l).1 _).2 le_rfl, fun e he m L₁ _ _ _ hL =>
    step0 hμ hγ (by omega) m L₁ hL⟩


end Step0

end UpperTheory.V.Tower

end
end
end
