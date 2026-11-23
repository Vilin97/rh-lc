module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfHodgeTateLatticeConstQpModZpEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfGhostThetaFrobIterValuesXiMuPadicStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSeparatesDualLieGhostComponentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupLatticeFreeRankHeightStatement
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.Frob

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frob_phiInv (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem phiInv_ofPadic' (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  ext n
  simp only [phiInv, ofPadic, RingHom.coe_comp, Function.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod
    (((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p))) (ZMod.castHom (dvd_refl p) (PreTilt O p))) _

theorem frob_ofPadic (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  conv_lhs => rw [← phiInv_ofPadic' c]
  exact frob_phiInv _

def frobT (G : PDivGroup p O) (y : TDual G) : TDual G where
  toFun t := WittVector.frobenius (y t)
  map_add' s t := by rw [map_add (f := _), map_add (f := _)]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, frob_ofPadic, smul_eq_mul]

def xiPhiInvT (ε : PreTilt O p) (G : PDivGroup p O) (m : TDual G) : TDual G where
  toFun t := xi ε * phiInv p O (m t)
  map_add' s t := by rw [map_add (f := _), map_add (f := _), mul_add]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, phiInv_ofPadic', smul_eq_mul, mul_left_comm]

def frobLatt (G : PDivGroup p O) :
    latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G where
  toFun y := ⟨frobT G y.1, fun n => by
    obtain ⟨x, hx⟩ := y.2 (n + 1)
    exact ⟨x, fun t => by rw [← hx]; rfl⟩⟩
  map_add' y z := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((y.1 + z.1) t) = _
    rw [LinearMap.add_apply, map_add (f := _)]; rfl
  map_smul' a y := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((a • y.1) t) = _
    rw [LinearMap.smul_apply, smul_eq_mul, map_mul]; rfl

end GlobalTheory.PDivLat.Frob


open GlobalTheory.PDivLat.Frob in
theorem GlobalTheory.PDivLat.exists_frobenius_latt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ φ : ∀ G : PDivGroup p O, latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G, (∀ G y t, (φ G y).1 t = WittVector.frobenius (y.1 t)) ∧ ∀ G m, ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  obtain ⟨-, -, -, h0, hs, hphi⟩ := GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε
  refine ⟨fun G => frobLatt G, fun G y t => rfl, fun G m => ?_⟩
  refine ⟨⟨xiPhiInvT ε G m.1, fun n => ?_⟩, ?_⟩
  · cases n with
    | zero => exact ⟨0, fun t => by
        show ghost p O 0 (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, h0, zero_mul, LinearMap.zero_apply]⟩
    | succ k =>
      obtain ⟨x, hx⟩ := m.2 k
      exact ⟨(p : O) • x, fun t => by
        show ghost p O (k + 1) (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, hs, hphi, hx, LinearMap.smul_apply, smul_eq_mul]⟩
  · apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius (xi ε * phiInv p O (m.1 t)) = _
    rw [map_mul, frob_phiInv]; rfl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinfStatement

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_frobenius_hodgeTateLattice_ainf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ φ : ∀ G : PDivGroup p O, latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G, (∀ G y t, (φ G y).1 t = WittVector.frobenius (y.1 t)) ∧ ∀ G m, ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m := by
  first | exact @GlobalTheory.PDivLat.exists_frobenius_latt | exact GlobalTheory.PDivLat.exists_frobenius_latt | (intros; apply GlobalTheory.PDivLat.exists_frobenius_latt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MemSmulOfTmulEqZero

section

@[expose] public section

open CategoryTheory TensorProduct ChangeOfRings

namespace GlobalTheory.CompanionTheory.ModuleReduction

theorem mem_smul_of_tmul_eq_zero {A Q N : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N] (g : A →ₗ[A] Q) (hg : Function.Surjective g) (ξ : A)
    (hk : ∀ a, g a = 0 ↔ ∃ b, a = ξ * b) (m : N) (h : g 1 ⊗ₜ[A] m = 0) :
    ∃ n : N, m = ξ • n := by
  have hex : Function.Exact (LinearMap.mulLeft A ξ) g := by
    intro a
    rw [hk a]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
  have hex' := rTensor_exact N hex hg
  have h1 : (LinearMap.rTensor N g) ((1 : A) ⊗ₜ[A] m) = 0 := by
    simpa using h
  obtain ⟨t, ht⟩ := (hex' _).1 h1
  have key : ∀ t : A ⊗[A] N, TensorProduct.lid A N (LinearMap.rTensor N (LinearMap.mulLeft A ξ) t)
      = ξ • TensorProduct.lid A N t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a n => simp [mul_smul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  refine ⟨TensorProduct.lid A N t, ?_⟩
  rw [← key, ht]
  simp

theorem exists_reduction (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O)
    (hθ : Function.Surjective θ) (ξ : A) (hker : RingHom.ker θ = Ideal.span {ξ})
    (𝒞 : Type 1) [CategoryTheory.Category.{0} 𝒞] (M : CategoryTheory.Functor 𝒞 (ModuleCat.{0} A)) :
    ∃ (D : CategoryTheory.Functor 𝒞 (ModuleCat.{0} O)) (r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] D.obj X),
      (∀ X, Function.Surjective (r X) ∧ ∀ m, r X m = 0 ↔ ∃ n, m = ξ • n) ∧
      ∀ (X Y : 𝒞) (f : X ⟶ Y) (m : M.obj X), D.map f (r X m) = r Y (M.map f m) := by
  let Q := (ModuleCat.restrictScalars θ).obj (ModuleCat.of O O)
  let one : Q := (1 : O)
  let g : A →ₗ[A] Q := LinearMap.toSpanSingleton A Q one
  have hgθ : ∀ a, (g a : O) = θ a := fun a => mul_one (θ a)
  have hsm : ∀ (X : 𝒞) (a : A) (m : M.obj X),
      (1 : O) ⊗ₜ[A,θ] (a • m) = (θ a) ⊗ₜ[A,θ] m := by
    intro X a m
    have h := TensorProduct.smul_tmul (R := A) (R' := A) a one m
    have e : a • one = (θ a : O) := hgθ a
    rw [e] at h
    exact h.symm
  let r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] (M ⋙ ModuleCat.extendScalars θ).obj X := fun X =>
    { toFun := fun m => (1 : O) ⊗ₜ[A,θ] m
      map_add' := fun a b => TensorProduct.tmul_add _ _ _
      map_smul' := fun a m => by
        refine (hsm X a m).trans ?_
        have := ModuleCat.ExtendScalars.smul_tmul θ (M := M.obj X) (θ a) (1 : O) m
        rw [mul_one] at this
        exact this.symm }
  refine ⟨M ⋙ ModuleCat.extendScalars θ, r, fun X => ⟨?_, fun m => ⟨?_, ?_⟩⟩, ?_⟩
  · intro y
    change Q ⊗[A] (M.obj X) at y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul o n =>
      obtain ⟨a, ha⟩ := hθ o
      refine ⟨a • n, ?_⟩
      refine (hsm X a n).trans ?_
      rw [ha]
      rfl
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      rw [map_add (f := _), hu, hv]
      rfl
  · intro h
    refine mem_smul_of_tmul_eq_zero g ?_ ξ ?_ m ?_
    · intro q
      obtain ⟨a, ha⟩ := hθ q
      exact ⟨a, (hgθ a).trans ha⟩
    · intro a
      have : g a = 0 ↔ θ a = 0 := by
        rw [← hgθ a]
        rfl
      rw [this, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
    · have e : g 1 = one := one_smul A one
      rw [e]
      exact h
  · rintro ⟨n, rfl⟩
    have : θ ξ = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.mem_span_singleton_self ξ
    change (1 : O) ⊗ₜ[A,θ] (ξ • n) = 0
    rw [hsm X ξ n, this]
    exact TensorProduct.zero_tmul (R := A) Q n
  · intro X Y f m
    rfl

end GlobalTheory.CompanionTheory.ModuleReduction
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SemilinearFactorsThroughReduction

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Div

theorem semilinear_factors_through_reduction :
    ∀ (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O), Function.Surjective θ →
      ∀ (ξ : A), θ ξ = 0 →
      ∀ (M D L : Type) [AddCommGroup M] [Module A M] [AddCommGroup D] [Module O D]
        [AddCommGroup L] [Module O L] (r : M →ₛₗ[θ] D) (q : M →ₛₗ[θ] L),
        Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = ξ • n) →
        ∃ π : D →ₗ[O] L, ∀ m, π (r m) = q m := by
  intro A O _ _ θ hθ ξ hξ M D L _ _ _ _ _ _ r q hr hker
  have hq : ∀ m m', r m = r m' → q m = q m' := by
    intro m m' h
    obtain ⟨n, hn⟩ := (hker (m - m')).1 (by rw [map_sub, h, sub_self])
    have h0 : q (m - m') = 0 := by rw [hn, map_smulₛₗ, hξ, zero_smul]
    rwa [map_sub, sub_eq_zero] at h0
  let s := Function.surjInv hr
  have hs : ∀ d, r (s d) = d := Function.surjInv_eq hr
  refine ⟨{ toFun := fun d => q (s d), map_add' := ?_, map_smul' := ?_ }, fun m => hq _ _ (hs _)⟩
  · intro d d'
    rw [← map_add (f := _)]
    exact hq _ _ (by rw [map_add (f := _), hs, hs, hs])
  · intro o d
    obtain ⟨a, rfl⟩ := hθ o
    simp only [RingHom.id_apply]
    rw [← map_smulₛₗ]
    exact hq _ _ (by rw [map_smulₛₗ, hs, hs])

end GlobalTheory.CompanionTheory.Div
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismaticDieudonneHodgeOfHodgeTateDatum

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat



theorem prismaticDieudonneHodgeAt_of_hasDatum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, HasDatum hε G) → GlobalTheory.Published.PrismaticDieudonneHodgeAt ε := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε hD
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by
    simpa only [zeta, Function.iterate_one, pow_one] using hε 1
  obtain ⟨hdom, -, hker, hθ, -, -, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  have hθξ : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _

  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.T.exists_frobenius_hodgeTateLattice_ainf p C v O hv ε hε

  have hLie := fun G : PDivGroup p O =>
    GlobalTheory.T.hodgeTate_separates_dual_lie_ghostComponent p C v O hv ε hε G (hD G)
  have hsep : ∀ (G : PDivGroup p O) (x x' : G.dual.Lie),
      (∀ t, x (hodgeTate G t) = x' (hodgeTate G t)) → x = x' := fun G x x' h =>
    sub_eq_zero.1 ((hLie G).1 (x - x') fun t => by
      rw [LinearMap.sub_apply, h, sub_self])
  have hqex : ∀ G : PDivGroup p O, ∃ q : latt G →ₛₗ[WittVector.fontaineTheta O p] G.dual.Lie,
      ∀ y t, q y (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t) := fun G => by
    choose x hx using fun y : latt G => y.2 0
    refine ⟨{ toFun := x
              map_add' := fun a b => hsep G _ _ (fun t => ?_)
              map_smul' := fun c a => hsep G _ _ (fun t => ?_) }, fun y t => (hx y t).symm⟩
    · rw [LinearMap.add_apply, ← hx, ← hx, ← hx]; exact ghost_add 0 (a.1 t) (b.1 t)
    · rw [LinearMap.smul_apply, ← hx, ← hx, smul_eq_mul]; exact ghost_mul 0 c (a.1 t)
  choose q hq using hqex

  have hadd : (lattFunctor p O).Additive :=
    { map_add := fun {X Y f g} => ModuleCat.hom_ext (LinearMap.ext fun y =>
        Subtype.ext (LinearMap.ext fun t => by
          change y.1 (tateMap _ _ O (f + g).unop t) =
            y.1 (tateMap _ _ O f.unop t) + y.1 (tateMap _ _ O g.unop t)
          rw [unop_add, map_add (f := _), LinearMap.add_apply, map_add (f := _)])) }

  have hred : ∃ (D : (PDivGroup p O)ᵒᵖ ⥤ ModuleCat.{0} O)
      (r : ∀ X : (PDivGroup p O)ᵒᵖ, latt X.unop →ₛₗ[WittVector.fontaineTheta O p] D.obj X),
      (∀ X, Function.Surjective (r X) ∧ ∀ m, r X m = 0 ↔ ∃ n, m = xi ε • n) ∧
      ∀ (X Y : (PDivGroup p O)ᵒᵖ) (f : X ⟶ Y) (m : latt X.unop),
        (D.map f).hom (r X m) = r Y (lattMap f.unop m) :=
    GlobalTheory.CompanionTheory.ModuleReduction.exists_reduction (Ainf p O) O
      (WittVector.fontaineTheta O p) hθ (xi ε) hker (PDivGroup p O)ᵒᵖ (lattFunctor p O)
  obtain ⟨D, r, hr, nr⟩ := hred

  have hπex : ∀ G : PDivGroup p O, ∃ π : D.obj (op G) →ₗ[O] G.dual.Lie,
      ∀ m, π (r (op G) m) = q G m := fun G =>
    GlobalTheory.CompanionTheory.Div.semilinear_factors_through_reduction (Ainf p O) O (WittVector.fontaineTheta O p) hθ
      (xi ε) hθξ _ (D.obj (op G)) G.dual.Lie (r (op G)) (q G) (hr (op G)).1 (hr (op G)).2
  choose π hπ using hπex

  have hιex := fun G : PDivGroup p O => GlobalTheory.T.exists_hodgeSequence_first_map_lattice p C v O hv ε hε G (hD G) (D.obj (op G))
    (r (op G)) (π G) (hr (op G)).1 (hr (op G)).2
    (fun y t => (LinearMap.congr_fun (hπ G y) (hodgeTate G t)).trans (hq G y t))
  choose ι hι using hιex
  have nr' : ∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : latt H),
      (D.map f.op).hom (r (op H) m) = r (op G) (lattMap f m) := fun G H f m => nr _ _ f.op m
  refine ⟨lattFunctor p O, D, φ, fun G => r (op G), ι, π, hadd, ?_⟩
  dsimp (config := { instances := true }) only [lattFunctor, Opposite.unop_op, Quiver.Hom.unop_op,
    ModuleCat.ofHom_apply, ModuleCat.hom_ofHom]
  refine ⟨?_, hφ2, ?_, fun G => hr (op G), nr', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun G => GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height p C v O hv ε hε G (hD G)
  · intro G H f m
    exact Subtype.ext (LinearMap.ext fun t =>
      (hφ1 H m (tateMap G H O f t)).trans (hφ1 G (lattMap f m) t).symm)
  · intro G
    refine ⟨(hι G).1, (hι G).2.1, fun x => ?_⟩
    obtain ⟨y, hy⟩ := (hLie G).2 x
    exact ⟨r (op G) y, (hπ G y).trans (hsep G _ _ fun t => (hq G y t).trans (hy t))⟩
  · intro G H f w
    exact GlobalTheory.T.pDivGroup_hodgeTateFirstMap_natural p C v O hv ε hε G H f (hD G) (hD H) (D.obj (op G)) (r (op G)) (D.obj (op H))
      (r (op H)) (D.map f.op).hom (ι G) (ι H) (hr (op G)).1 (hr (op G)).2 (nr' G H f)
      (hι G).2.2 (hι H).2.2 w
  · intro G H f x
    obtain ⟨m, rfl⟩ := (hr (op H)).1 x
    let ℓ := lieMap H.dual G.dual (dualHom G H f)
    have hqf : q G (lattMap f m) = ℓ (q H m) := hsep G _ _ fun t =>
      (hq G (lattMap f m) t).trans
        ((hq H m (tateMap G H O f t)).symm.trans (congrArg (q H m) (hodgeTate_tateMap f t)))
    exact (congrArg (π G) (nr' G H f m)).trans
      ((hπ G (lattMap f m)).trans (hqf.trans (congrArg ℓ (hπ H m).symm)))
  · obtain ⟨e, he⟩ := GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv p C v O hv ε hε
    exact ⟨e, fun m => (he (φ (const p O) m)).trans
      ((hφ1 (const p O) m (constGen p O)).trans (congrArg WittVector.frobenius (he m).symm))⟩
  · obtain ⟨e, he⟩ := GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one p C v O hv ε hε
    have : IsDomain (Ainf p O) := hdom
    have hμ : Sandwich.mu ε ≠ 0 := fun h => GlobalTheory.Dieudonne.not_dvd_mu hε1 (h ▸ dvd_zero _)
    refine ⟨e, fun m => mul_left_cancel₀ hμ ?_⟩
    have h1 : Sandwich.mu ε * e (φ _ m) = WittVector.frobenius (Sandwich.mu ε * e m) :=
      (he (φ (PDivGroup.mu p O) m)).trans
        ((hφ1 (PDivGroup.mu p O) m (epsTate hε)).trans (congrArg WittVector.frobenius (he m).symm))
    have h2 : WittVector.frobenius (Sandwich.mu ε * e m) =
        Sandwich.mu ε * (WittVector.frobenius (xi ε) * WittVector.frobenius (e m)) := by
      exact ((WittVector.frobenius : Ainf p O →+* Ainf p O).map_mul _ _).trans
        ((congrArg (· * WittVector.frobenius (e m)) (GlobalTheory.Dieudonne.frobenius_mu ε)).trans
          ((mul_assoc _ _ _).trans (mul_left_comm _ _ _)))
    exact h1.trans h2
  · change ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O),
        (∀ m, g (φ (PDivGroup.mu p O) m) = φ (const p O) (g m)) →
          ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g
    intro g hg
    refine GlobalTheory.T.existsUnique_muPInfinity_hodgeTate_lattice_map p C v O hv ε hε g ?_
    intro m m' hm t
    have e : m' = φ (PDivGroup.mu p O) m :=
      Subtype.ext (LinearMap.ext fun s => (hm s).trans (hφ1 (PDivGroup.mu p O) m s).symm)
    exact (congrArg (fun z : latt (PDivGroup.mu p O) => (g z).1 t) e).trans
      ((congrArg (fun z : latt (const p O) => z.1 t) (hg m)).trans (hφ1 (const p O) (g m) t))

end GlobalTheory.PDivLat
end
end
end
