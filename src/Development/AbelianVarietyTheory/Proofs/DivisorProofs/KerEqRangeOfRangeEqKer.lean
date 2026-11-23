module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneRanksFieldCharP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRigExtMapRelFrobLeRangeRigOfOmegaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFrobeniusPullbackCotangentModVersc
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulId
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFrobeniusPullbackCotangentModVerscStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K)
    (w : Cot K ((PDivGroup.frobTwist h G).A 1)) :
    ∃ (β : (PDivGroup.frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((PDivGroup.relFrob h G).app 1 β) = 0 ∧
        dUnit (R := K) β = w + cotMap ((PDivGroup.verschiebung h G).app 1) w' :=
  PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq p K h G w
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelIdealOfAppEqZeroField

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_comp_of_app_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G) (hfg : f ≫ g = (p : ℤ_[p]) • 𝟙 G)
    (a : G.A 1) (ha : g.app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp (f.app 1)) := by
  set K := kerIdeal ((G.mulP 1).comp (f.app 1)) with hK
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff ((G.mulP 1).comp (f.app 1)) x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp (f.app 2 : H.A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal (R := R) (A := H.A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff _ y).2 fun z => by
      have e : f.app 2 (mulBy R _ p z) = G.mulP 1 (f.app 1 (H.res 1 z)) := by
        rw [map_mulBy, ← PDivGroup.res_app, mulP_res]
      have := hx (H.res 1 z)
      rw [CoalgHomClass.counit_comp_apply] at this
      exact (congrArg x e).trans this
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app] at ha
  have hb : g.app 2 b ∈ torsionIdeal (R := R) (A := H.A 2) p := by
    have : g.app 2 b ∈ torsionIdeal (R := R) (A := H.A 2) (p ^ 1) := by
      rw [← H.ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x (f.app 2 (g.app 2 b)) = 0 := hy hb
  have e2 : f.app 2 (g.app 2 b) = mulBy R _ p b := by
    have := congrArg (fun φ : G ⟶ G => φ.app 2 b) hfg
    simp only [comp_app, natCast_smul_id_app] at this
    exact this
  rw [e2] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup


open GlobalTheory.PDivGroup in
theorem GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G →
    g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  intro p _ K _ G H f g hfg _ a ha
  have hmulP : Function.Injective (G.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := K) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := G.dual_mulP_surjective 1 φ
    change ψ.ofConv (G.mulP 1 a) = ψ.ofConv (G.mulP 1 b)
    rw [e]
  have h1 := mulP_mem_kerIdeal_comp_of_app_eq_zero p K G H f g hfg a ha
  rw [kerIdeal_comp] at h1
  rw [← GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective K _ _ (G.mulP 1) hmulP (kerIdeal (f.app 1))]
  exact h1
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelIdealOfAppEqZeroFieldStatement

section

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.mem_kernel_ideal_of_app_eq_zero_field : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G → g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  first | exact @GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero | exact GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero | (intros; apply GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRigOfOmegaLeRangeRigExtMapVerschiebung

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem range_rigOfOmega_le_range_rigExtMap_verschiebung :
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K),
      LinearMap.range (frobTwist h G).rigOfOmega ≤
        LinearMap.range (rigExtMap (verschiebung h G)) := by
  intro p _ K _ h G
  rintro _ ⟨w, rfl⟩
  obtain ⟨β, w', hβ, hd⟩ :=
    GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung p K h G (-(w.1 1))
  obtain ⟨-, c, B₀, -, hB₀, -, hB₀'⟩ := exists_of_cobOne_eq_zero hβ
  obtain ⟨B, hB⟩ : cocyclesMap (verschiebung h G) c ∈ LinearMap.range (frobTwist h G).cob :=
    (Submodule.Quotient.mk_eq_zero _).1
      (LinearMap.congr_fun (vecExtMap_verschiebung h G) (Submodule.Quotient.mk c))
  have h1 : funsMap (relFrob h G) B - B₀ = 0 := G.eq_zero_of_cob_eq_zero h (by
    rw [map_sub, ← cocyclesMap_cob, hB, hB₀, ← relFrob_comp_verschiebung h G, sub_eq_zero]
    exact Subtype.ext (funext fun _ => (pullTwo_comp _ _ _).symm))
  have h2 : (relFrob h G).app 1 (B.1 1 - β) = 0 := by
    rw [map_sub, ← hB₀']
    exact congrArg (fun z : G.funs => z.1 1) h1
  obtain ⟨w'', hw''⟩ := dUnit_mem_range_of_mem_kerIdeal _
    (GlobalTheory.T.mem_kernel_ideal_of_app_eq_zero_field p K _ _ (verschiebung h G) (relFrob h G) (verschiebung_comp_relFrob h G)
      (relFrob_comp_verschiebung h G) _ h2)
  obtain ⟨u, hu⟩ := G.omegaLevel_surjective 1 (w' + w'')
  have h3 : (frobTwist h G).dFun B = omegaMap _ _ (verschiebung h G) u - w :=
    ((frobTwist h G).omegaLevel_one_bijective h).1 (by
      rw [map_sub, omegaLevel_apply, omegaLevel_apply, omegaLevel_apply, omegaMap_val,
        ← omegaLevel_apply, ← omegaLevel_apply _ _ u, hu, map_add, hw'']
      change dUnit (R := K) (B.1 1) = _
      rw [dUnit, dUnit, map_sub, ← dUnit, ← dUnit, hd]
      abel)
  refine ⟨G.rigMk (c, u), ?_⟩
  rw [rigExtMap_mk]
  refine (Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩
  · exact hB.trans (sub_zero _).symm
  · exact h3

end GlobalTheory.PDivGroup
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRigOfOmegaLeRangeRigExtMapVerschiebungStatement

section

@[expose] public section

open GlobalTheory

theorem _root_.GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung'
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    LinearMap.range (PDivGroup.frobTwist h G).rigOfOmega ≤
      LinearMap.range (PDivGroup.rigExtMap (PDivGroup.verschiebung h G)) :=
  PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung p K h G
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulIdStatement

section

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G H : PDivGroup p R), (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧ rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  first | exact @GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | exact GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | (intros; apply GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory

namespace PDivGroup

open PDiv

theorem ker_eq_range_of_range_eq_ker {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (_ : Module.Finite K V) (_ : Module.Finite K W) (f : V →ₗ[K] W)
    (g : W →ₗ[K] V) (hd : Module.finrank K V = Module.finrank K W) (h0 : g ∘ₗ f = 0)
    (h1 : LinearMap.range g = LinearMap.ker f) : LinearMap.ker g = LinearMap.range f := by
  have e1 := g.finrank_range_add_finrank_ker
  have e2 := f.finrank_range_add_finrank_ker
  rw [h1] at e1
  exact (Submodule.eq_of_le_of_finrank_eq (LinearMap.range_le_ker_iff.2 h0) (by omega)).symm

theorem rigExt_field_of_charP (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧
    Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height ∧
    LinearMap.range (rigExtMap (verschiebung h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (relFrob h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (verschiebung h G)) = LinearMap.range (rigExtMap (relFrob h G)) ∧
    LinearMap.range (rigExtMap (relFrob h G)) =
      Submodule.span K (Set.range fun x : G.RigExt => SemiHom.rig (absFrob h G) x) := by
  obtain ⟨-, f1, d1, d2⟩ := GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G
  obtain ⟨-, f2, d3, -⟩ := GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h (frobTwist h G)
  have h4 := le_antisymm (range_rigExtMap_verschiebung_le h G) (GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung' p K h G)
  have h5 := le_antisymm (GlobalTheory.T.ker_rigExtMap_relFrob_le_range_rigOfOmega' p K h G)
    (LinearMap.range_le_ker_iff.2 (rigExtMap_relFrob_comp_rigOfOmega h G))
  have h6 : rigExtMap (verschiebung h G) ∘ₗ rigExtMap (relFrob h G) = 0 := by
    rw [← rigExtMap_comp, verschiebung_comp_relFrob]
    exact (GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id p K h
      (frobTwist h G) (frobTwist h G)).2
  exact ⟨f1, d1, d2, h4, h5, ker_eq_range_of_range_eq_ker f2 f1 _ _
    (d3.trans ((frobTwist_height h G).trans d1.symm)) h6 (h4.trans h5.symm),
    range_rigExtMap_relFrob h G⟩

end PDivGroup

end GlobalTheory
end
end
end
