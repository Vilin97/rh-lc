module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.LatticeTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimsLeHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIdeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebungStatement

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.PDivGroup.CotDim in
theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] (hp : (p : k) = 0) (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  have : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hp
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((relFrob hp Γ.dual).app 1)
  have haD : p ^ Module.finrank k (Cot k (Γ.dual.A 1)) ≤
      Module.finrank k (Γ.dual.A 1 ⧸ kerIdeal ((relFrob hp Γ.dual).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.dual.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ.dual 1))

  have hker : LinearMap.ker ((verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k := fun a ha => by
    have h1 : Γ.mulP 1 a ∈ kerIdeal ((Γ.mulP 1).comp ((relFrob hp Γ).app 1)) := by
      change (verschiebung hp Γ).app 1 a = 0 at ha
      let K := kerIdeal ((Γ.mulP 1).comp ((relFrob hp Γ).app 1))
      let x := Ideal.Quotient.mkₐ k K
      have hx := (kerIdeal_le_ker_iff ((Γ.mulP 1).comp ((relFrob hp Γ).app 1)) x).1
        fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
      let y := x.comp ((relFrob hp Γ).app 2 : (frobTwist hp Γ).A 2 →ₐ[k] Γ.A 2)
      have hy : torsionIdeal (R := k) (A := (frobTwist hp Γ).A 2) p ≤ RingHom.ker y :=
        (kerIdeal_le_ker_iff _ y).2 fun z => by
          have e : (relFrob hp Γ).app 2 (mulBy k _ p z) =
              Γ.mulP 1 ((relFrob hp Γ).app 1 ((frobTwist hp Γ).res 1 z)) := by
            rw [map_mulBy, ← PDivGroup.res_app, mulP_res]
          have h := hx ((frobTwist hp Γ).res 1 z)
          rw [CoalgHomClass.counit_comp_apply] at h
          exact (congrArg x e).trans h
      obtain ⟨b, rfl⟩ := Γ.res_surjective 1 a
      rw [← PDivGroup.res_app] at ha
      have hb : (verschiebung hp Γ).app 2 b ∈
          torsionIdeal (R := k) (A := (frobTwist hp Γ).A 2) p := by
        have h : (verschiebung hp Γ).app 2 b ∈ RingHom.ker ((frobTwist hp Γ).res 1) := ha
        simpa only [(frobTwist hp Γ).ker_res 1, pow_one] using h
      have h : x ((relFrob hp Γ).app 2 ((verschiebung hp Γ).app 2 b)) = 0 := hy hb
      rw [relFrob_app_verschiebung_app] at h
      rw [mulP_res]
      exact Ideal.Quotient.eq_zero_iff_mem.1 h
    rw [kerIdeal_comp] at h1
    rw [Submodule.restrictScalars_mem,
      ← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP (kerIdeal ((relFrob hp Γ).app 1))]
    exact h1
  have hV : Module.finrank k (LinearMap.range ((relFrob hp Γ.dual).app 1 :
        (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) +
      Module.finrank k (LinearMap.ker ((verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap) = Module.finrank k (Γ.A 1) := by
    let e : Γ.dual.A 1 ≃ₗ[k] Module.Dual k (Γ.A 1) := CartierDual.toDual k (Γ.A 1)
    let W := LinearMap.range ((relFrob hp Γ.dual).app 1 :
      (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap
    change Module.finrank k W + _ = _
    have hAnn : LinearMap.ker ((verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap =
        (W.map e.toLinearMap).dualCoannihilator := by
      ext a
      rw [Submodule.mem_dualCoannihilator, LinearMap.mem_ker]
      change (verschiebung hp Γ).app 1 a = 0 ↔ _
      constructor
      · rintro ha _ ⟨_, ⟨x, rfl⟩, rfl⟩
        change e ((relFrob hp Γ.dual).app 1 x) a = 0
        induction x using frobTwist_induction hp (G := Γ.dual) 1 with
        | h0 => simp
        | h2 x y hx hy =>
          rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
        | h1 r χ =>
          rw [map_smul, map_smul, LinearMap.smul_apply, relFrob_app_frobProj]
          have h := frobTwistDual_verschiebung hp 1 χ a
          rw [ha, map_zero] at h
          exact (congrArg (r • ·) h.symm).trans (smul_zero r)
      · intro ha
        refine frobTwist_ext_dual hp 1 fun χ => ?_
        rw [frobTwistDual_verschiebung, map_zero]
        refine ha _ ⟨_, ⟨(frobProj hp Γ.dual).app 1 χ, rfl⟩, ?_⟩
        exact congrArg e (relFrob_app_frobProj hp (G := Γ.dual) 1 χ)
    rw [hAnn, ← e.finrank_map_eq W]
    exact Subspace.finrank_add_finrank_dualCoannihilator_eq _
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have haA : p ^ Module.finrank k (Cot k (Γ.A 1)) ≤
      Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ 1))
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((relFrob hp Γ.dual).app 1 :
        (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  have key : p ^ (Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1))) ≤
      p ^ Γ.height := by
    rw [pow_add, mul_comm, ← hdimD, hord]
    exact Nat.mul_le_mul haD (haA.trans hrD)
  exact (Nat.pow_le_pow_iff_right hp2).1 key
