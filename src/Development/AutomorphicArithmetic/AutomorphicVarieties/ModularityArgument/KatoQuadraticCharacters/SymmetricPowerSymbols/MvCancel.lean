module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.KaU

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

namespace UpperTheory.V.Z.Kato.Sym.PE

theorem kaU : KaU := by
  intro Ω _ _ _ ε X m hm θ hθ g h hgz hhz hgm hhm
  haveI : NeZero m := NeZero.of_pos hm
  obtain ⟨hprim, hrep, hlg, -⟩ := lgB Ω ε X m hm
  have hpow : zt X m ^ m = 1 := hprim.pow_eq_one
  have hgθ : g θ = zt X m ^ (ka X m θ g).val * θ := hrep (g θ) θ hθ (by rw [← map_pow, hgm])
  have hhθ : h θ = zt X m ^ (ka X m θ h).val * θ := hrep (h θ) θ hθ (by rw [← map_pow, hhm])
  have hadd : ∀ i j : ZMod m, zt X m ^ i.val * zt X m ^ j.val = zt X m ^ (i + j).val := by
    intro i j
    rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hpow]
  have hhg : h (g θ) = zt X m ^ (ka X m θ h).val * g θ := by
    rw [hgθ, map_mul, map_pow, hhz, hhθ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · refine hlg _ _ _ hθ ?_
    show g (h θ) = _
    rw [hhθ, map_mul, map_pow, hgz, hgθ, ← mul_assoc, hadd, add_comm]
  · exact hlg _ _ _ ((map_ne_zero g).2 hθ) hhg
  · refine hlg _ _ _ hθ ?_
    show g.symm (h (g θ)) = _
    have e2 : g.symm (zt X m) = zt X m := by
      rw [RingEquiv.symm_apply_eq, hgz]
    rw [hhg, map_mul, map_pow, e2, RingEquiv.symm_apply_apply]

end UpperTheory.V.Z.Kato.Sym.PE
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtEx

section

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.ptEx :
    UpperTheory.V.Z.Kato.Sym.PtEx := by
  intro Ω _ _ _ ε X m hm u v hu hv
  have LG := lgB Ω ε X m hm
  have KU := PE.kaU Ω ε X m hm
  have hu0 : u ≠ 0 := hu.1
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (io X u) hm
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (io X v) hm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at ha
    exact hu0 ((map_eq_zero_iff _ (io X).injective).mp ha.symm)
  obtain ⟨η, hη, hlc, hunr⟩ := PE.etaEx Ω ε X m hm u v a b hu hv ha hb
  have hinU : ∀ g, InD X g → PE.InU X u v g := fun g hg => ⟨fun c => hg _, hg _, hg _, hg _⟩
  refine ⟨⟨a, b, η⟩, ⟨hu, hv, ha, hb, fun g h hg hh => hη g h (hinU g hg) (hinU h hh), hlc, hunr⟩, ?_⟩
  intro γ hu' hv'
  obtain ⟨σ, hσ⟩ := (admB Ω ε X).2.2.2.2.2.2.1 (slR X (ofSL γ))
  have hfix : ∀ f, X.sl (ofSL γ) f = f → σ (io X f) = io X f := fun f hf => by
    rw [hσ f]
    exact congrArg _ hf
  have hσU : PE.InU X u v σ :=
    ⟨fun c => hfix _ ((X.sl (ofSL γ)).commutes c), hfix _ (X.j_inv γ), hfix _ hu', hfix _ hv'⟩
  have hinv : ∀ x, σ x = x → σ⁻¹ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    exact σ.symm_apply_apply x
  have hσiU : PE.InU X u v σ⁻¹ :=
    ⟨fun c => hinv _ (hσU.1 c), hinv _ hσU.2.1, hinv _ hσU.2.2.1, hinv _ hσU.2.2.2⟩
  have hz : ∀ g, PE.InU X u v g → g (zt X m) = zt X m := fun g hg => by
    unfold zt
    exact hg.1 _
  have hka1 : ka X m a 1 = 0 := by
    show lg X m a a = 0
    exact LG.2.2.1 a a 0 ha0 (by simp)
  have hk1 : ∀ g : RingAut (Kb X), ka X m 1 g = 0 := fun g => by
    show lg X m (g 1) 1 = 0
    rw [map_one]
    exact LG.2.2.1 1 1 0 one_ne_zero (by simp)
  have hcyc : cyc (Ω := Ω) m 1 = 1 := (LG.2.2.2.2.2.2 1 1).2.1
  have hη1 : η 1 = 0 := by
    have := hη 1 1 (hinU 1 (fun _ => rfl)) (hinU 1 (fun _ => rfl))
    rw [mul_one, hka1] at this
    linear_combination -this
  unfold Mv
  refine ⟨σ, hσ, ?_⟩
  simp only [IsKum, dif, Pt.mv]
  refine ⟨1, by simp, fun h hh => ?_⟩
  have hhU := hinU h hh
  have E1 := hη σ⁻¹ (h * σ) hσiU ⟨fun c => by show h (σ _) = _; rw [hσU.1 c, hhU.1 c], by show h (σ _) = _; rw [hσU.2.1, hhU.2.1], by show h (σ _) = _; rw [hσU.2.2.1, hhU.2.2.1], by show h (σ _) = _; rw [hσU.2.2.2, hhU.2.2.2]⟩
  have E2 := hη h σ hhU hσU
  have E3 := hη σ⁻¹ σ hσiU hσU
  rw [inv_mul_cancel, hη1] at E3
  have K1 := (KU b (by rintro rfl; rw [zero_pow hm.ne'] at hb; exact hv.1 ((map_eq_zero_iff _ (io X).injective).mp hb.symm)) h σ (hz h hhU) (hz σ hσU) (by rw [hb]; exact hhU.2.2.2) (by rw [hb]; exact hσU.2.2.2)).1
  have K2 := (KU a ha0 σ⁻¹ σ (hz _ hσiU) (hz σ hσU) (by rw [ha]; exact hσiU.2.2.1) (by rw [ha]; exact hσU.2.2.1)).1
  rw [inv_mul_cancel, hka1] at K2
  rw [hk1, hcyc, mul_assoc]
  show 0 = 1 ^ 2 * η (σ⁻¹ * (h * σ)) - η h + ka X m a h * ka X m b σ - ka X m a σ * ka X m b h
  linear_combination (-1 : ZMod m) * E1 - E2 + E3 + ka X m a σ⁻¹ * K1 - ka X m b h * K2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvCancel

section

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {m : ℕ}

omit [IsAlgClosure ℚ Ω] in
private theorem sl_sl (γ δ : SL(2, ℤ)) (f : X.K) :
    X.sl (ofSL (γ * δ)) f = X.sl (ofSL δ) (X.sl (ofSL γ) f) := by
  rw [map_mul, X.sl_mul]

omit [IsAlgClosure ℚ Ω] in
private theorem sl_inv (γ : SL(2, ℤ)) (f : X.K) : X.sl (ofSL γ⁻¹) (X.sl (ofSL γ) f) = f := by
  rw [← sl_sl, mul_inv_cancel, map_one, X.sl_one]

private theorem mv_comp (hm : 0 < m) (γ δ : SL(2, ℤ)) {u v : X.K} {P Q R : Pt X m} (hP : IsPt X m u v P)
    (hQ : IsPt X m (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q)
    (hR : IsPt X m (X.sl (ofSL δ) (X.sl (ofSL γ) u)) (X.sl (ofSL δ) (X.sl (ofSL γ) v)) R) {f : X.Kˣ}
    (h1 : Mv X m (slR X (ofSL γ)) 1 P Q 1) (h2 : Mv X m (slR X (ofSL δ)) 1 Q R f) :
    Mv X m (slR X (ofSL (γ * δ))) 1 P R f := by
  have key := mvComp Ω ε X m hm (slR X (ofSL γ)) (slR X (ofSL δ)) 1 1 ((admB Ω ε X).1 _)
    ((admB Ω ε X).1 _) u v P Q R hP hQ hR 1 f h1 h2
  have he : (slR X (ofSL γ)).trans (slR X (ofSL δ)) = slR X (ofSL (γ * δ)) := by
    ext x
    show X.sl (ofSL δ) (X.sl (ofSL γ) x) = X.sl (ofSL (γ * δ)) x
    exact (sl_sl X γ δ x).symm
  rw [he, mul_one, map_one, one_pow, one_mul] at key
  exact key

private theorem mv_cancel (hm : 0 < m) (γ δ : SL(2, ℤ)) {u v : X.K} {P Q R : Pt X m} (hP : IsPt X m u v P)
    (hQ : IsPt X m (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q)
    (hR : IsPt X m (X.sl (ofSL δ) (X.sl (ofSL γ) u)) (X.sl (ofSL δ) (X.sl (ofSL γ) v)) R)
    (h1 : Mv X m (slR X (ofSL γ)) 1 P Q 1) (h2 : Mv X m (slR X (ofSL (γ * δ))) 1 P R 1) :
    Mv X m (slR X (ofSL δ)) 1 Q R 1 := by
  have hA := admB Ω ε X
  obtain ⟨f, -, hf⟩ := (mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u)
    (X.sl (ofSL γ) v) Q hQ).1 R hR
  have h3 := mv_comp X hm γ δ hP hQ hR h1 hf
  have hR' : IsPt X m (X.sl (ofSL (γ * δ)) u) (X.sl (ofSL (γ * δ)) v) R := by
    rw [sl_sl X γ δ u, sl_sl X γ δ v]
    exact hR
  obtain ⟨k, hk⟩ := ((mvEx Ω ε X m hm (slR X (ofSL (γ * δ))) 1 (hA.1 _) u v P hP).2.2.2
    R hR' 1 f h2).mp h3
  refine ((mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u)
    (X.sl (ofSL γ) v) Q hQ).2.2.2 R hR f 1 hf).mpr ⟨k⁻¹, ?_⟩
  rw [hk, one_mul, inv_pow, mul_inv_cancel]

omit [IsAlgClosure ℚ Ω] in
private theorem rep_ex : ∃ (r : X.K × X.K → X.K × X.K) (g : X.K × X.K → SL(2, ℤ)),
    (∀ p, X.sl (ofSL (g p)) (r p).1 = p.1 ∧ X.sl (ofSL (g p)) (r p).2 = p.2) ∧
    ∀ (p : X.K × X.K) (γ : SL(2, ℤ)), r (X.sl (ofSL γ) p.1, X.sl (ofSL γ) p.2) = r p := by
  let S : Setoid (X.K × X.K) :=
    { r := fun p q => ∃ g : SL(2, ℤ), X.sl (ofSL g) p.1 = q.1 ∧ X.sl (ofSL g) p.2 = q.2
      iseqv := ⟨fun p => ⟨1, by rw [map_one, X.sl_one], by rw [map_one, X.sl_one]⟩,
        fun ⟨g, h1, h2⟩ => ⟨g⁻¹, by rw [← h1, sl_inv], by rw [← h2, sl_inv]⟩,
        fun ⟨g, h1, h2⟩ ⟨k, k1, k2⟩ => ⟨g * k, by rw [sl_sl, h1, k1], by rw [sl_sl, h2, k2]⟩⟩ }
  refine ⟨fun p => (Quotient.mk S p).out, fun p => Classical.choose (Quotient.mk_out (s := S) p),
    fun p => Classical.choose_spec (Quotient.mk_out (s := S) p), fun p γ => ?_⟩
  show (Quotient.mk S _).out = (Quotient.mk S p).out
  rw [Quotient.sound (s := S) ⟨γ⁻¹, sl_inv X γ p.1, sl_inv X γ p.2⟩]

end

theorem UpperTheory.V.Z.Kato.Sym.secEx :
    UpperTheory.V.Z.Kato.Sym.SecEx := by
  intro Ω _ _ _ ε X m hm
  obtain ⟨r, g, hg, hr⟩ := rep_ex X
  have hA := admB Ω ε X
  haveI : Nonempty (Pt X m) := ⟨⟨0, 0, fun _ => 0⟩⟩
  have hUsl : ∀ (γ : SL(2, ℤ)) (a : X.K), IsU X a → IsU X (X.sl (ofSL γ) a) :=
    fun γ a ha => (hA.2.2.2.2.2.1 _ _ (hA.1 (ofSL γ))).1 a ha
  let Good : X.K → X.K → Pt X m → Prop := fun a b P => IsPt X m a b P ∧
    ∀ γ : SL(2, ℤ), X.sl (ofSL γ) a = a → X.sl (ofSL γ) b = b → Mv X m (slR X (ofSL γ)) 1 P P 1
  let P0 : X.K → X.K → Pt X m := fun a b => Classical.epsilon (Good a b)
  have hP0 : ∀ a b, IsU X a → IsU X b → Good a b (P0 a b) :=
    fun a b ha hb => Classical.epsilon_spec (ptEx Ω ε X m hm a b ha hb)
  have hrep : ∀ a b, X.sl (ofSL (g (a, b))) (r (a, b)).1 = a ∧
      X.sl (ofSL (g (a, b))) (r (a, b)).2 = b := fun a b => hg (a, b)
  have hrU : ∀ a b, IsU X a → IsU X b → IsU X (r (a, b)).1 ∧ IsU X (r (a, b)).2 := by
    intro a b ha hb
    have e1 := congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).1
    have e2 := congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).2
    simp only [sl_inv] at e1 e2
    rw [e1, e2]
    exact ⟨hUsl _ a ha, hUsl _ b hb⟩
  let t : X.K → X.K → Pt X m := fun a b => Classical.epsilon (fun Q => IsPt X m a b Q ∧
    Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1)
  have ht : ∀ a b, IsU X a → IsU X b → IsPt X m a b (t a b) ∧
      Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) (t a b) 1 := by
    intro a b ha hb
    obtain ⟨h1, h2⟩ := hrU a b ha hb
    obtain ⟨Q, hQ, hM⟩ := (mvEx Ω ε X m hm (slR X (ofSL (g (a, b)))) 1 (hA.1 _) _ _ _
      (hP0 _ _ h1 h2).1).2.1
    change IsPt X m (X.sl (ofSL (g (a, b))) (r (a, b)).1)
      (X.sl (ofSL (g (a, b))) (r (a, b)).2) Q at hQ
    rw [(hrep a b).1, (hrep a b).2] at hQ
    exact Classical.epsilon_spec (p := fun Q => IsPt X m a b Q ∧
      Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1) ⟨Q, hQ, hM⟩
  refine ⟨t, fun u v hu hv => ⟨(ht u v hu hv).1, fun γ => ?_⟩⟩
  have hu' := hUsl γ u hu
  have hv' := hUsl γ v hv
  have hrr : r (X.sl (ofSL γ) u, X.sl (ofSL γ) v) = r (u, v) := hr (u, v) γ
  obtain ⟨hQt, hMa⟩ := ht u v hu hv
  obtain ⟨hRt, hMb⟩ := ht _ _ hu' hv'
  obtain ⟨q1, q2⟩ := hrU u v hu hv
  have hgood := hP0 _ _ q1 q2
  obtain ⟨e1, e2⟩ := hrep u v
  obtain ⟨f1, f2⟩ := hrep (X.sl (ofSL γ) u) (X.sl (ofSL γ) v)
  rw [hrr] at hMb f1 f2
  have hs1 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).1
      = (r (u, v)).1 := by
    rw [sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e1]
    have k := sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).1
    rw [f1] at k
    exact k
  have hs2 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).2
      = (r (u, v)).2 := by
    rw [sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e2]
    have k := sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).2
    rw [f2] at k
    exact k
  have stab := hgood.2 _ hs1 hs2
  have comp := mv_comp X hm _ (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) hgood.1
    (by rw [hs1, hs2]; exact hgood.1) (by rw [hs1, hs2, f1, f2]; exact hRt) stab hMb
  rw [inv_mul_cancel_right] at comp
  exact mv_cancel X hm (g (u, v)) γ hgood.1 (by rw [e1, e2]; exact hQt)
    (by rw [e1, e2]; exact hRt) hMa comp
end
end
