module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero

-- Source module: Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.FewBadPrimes

section

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField GlobalTheory.EX

variable {R : Ranks}

def condE (H : Host R) : ℕ := H.QS * H.q * H.d

def dlogH (H : Host R) : ℝ :=
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction
      ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ H.d)) 1 /
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ H.d) 1).re

def frobH (H : Host R) (p : ℕ) : R.A :=
  R.iotaInv (Classical.epsilon (fun g : R.GG =>
    g ∈ {g : R.GG | ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ∧ H.galE σ = g})).2

def logPowerBoundClassPrimes (H : Host R) (s : Scale) : ℕ :=
  2 * sSup {l | ∃ p : ℕ, p.Prime ∧ H.cls p = PrimeClass.inertClass ∧
    l = ⌈Real.logb p (((R.k : ℝ) * s.x ^ Scale.A) ^ 4)⌉₊}

def GoodH (H : Host R) (s : Scale) (p : ℕ) (t0 : R.A) : Prop :=
  G.IsGoodOrbit (addOrderOf (frobH H p))
    (Finset.univ.filter (fun i : Fin (addOrderOf (frobH H p)) => t0 + (i : ℕ) • frobH H p ∈ H.TT))
    (logPowerBoundClassPrimes H s) (G.KG s) (G.rG s) s.delta1 (G.hG s) s.x

def IsOrigins {φ : Formalism.HC.Frame} (bs : φ.A → φ.A → φ.A) : Prop :=
  (∀ h t, ∃ i : ℕ, bs h t + i • h = t) ∧ ∀ h t, bs h (t + h) = bs h t


open Classical in
def FewBad (H : Host R) (s : Scale) (bs : R.A → R.A → R.A) : Prop :=
  ∑ p ∈ (Finset.range ⌈s.X'⌉₊).filter (fun p => p.Prime ∧ H.cls p = PrimeClass.inertClass ∧
      s.x ^ (s.eps / 4) ≤ (addOrderOf (frobH H p) : ℝ)),
    Real.log p / p * ((H.TT.filter (fun t => ¬ GoodH H s p (bs (frobH H p) t))).card : ℝ) ≤
  (H.TT.card : ℝ) * s.x ^ (-2 + s.eps)

def CharOf (H : Host R) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ ∃ ψ : R.GG →* ℂˣ, ∀ (a : ℕ) (h : a.Coprime H.condN),
    χ (a : ZMod N) = ((ψ (H.art (ZMod.unitOfCoprime a h)) : ℂˣ) : ℂ)

def RealBoxes (H : Host R) (Y eps : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), CharOf H χ → GlobalTheoryTheory.IsRealChar χ →
    (H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps * GlobalTheoryTheory.X2 Y eps) χ) ∧
    (H.q ∣ N → ¬ H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps) χ)

def BoxesInWindow (s : Scale) (H : Host R) : Prop :=
  ∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H ∧ Boxq Y s.eps H.q H.d ∧ RealBoxes H Y s.eps

def ArithData (C : FC) (s : Scale) (H : Host R) (q0 : ℕ)
    (bs : R.A → R.A → R.A) : Prop :=
  HostVal s C.P.Cpde H ∧ H.CT2 = C.CT2 ∧
  BoxesInWindow s H ∧ |dlogH H| ≤ s.x ^ s.eps ∧ QDq s.x s.eps 4 H.q H.d ∧
  4 * H.Lw * H.T2.card ≤ R.n0 ∧
  IsOrigins bs ∧ FewBad H s bs ∧
  (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E) ∧
    π - 1 ∈ Ideal.span {((condE H : ℕ) : 𝓞 H.E)}) ∧
  Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧
  (H.pde ≡ 1 [MOD Nat.lcm 15 (condE H)] ∧ H.pde' ≡ 1 [MOD Nat.lcm 15 (condE H)]) ∧
  (q0.Prime ∧ 5 ≤ q0 ∧ (q0 : ℝ) ≤ (condE H : ℝ) ^ C.P.Cpde ∧
    ∃ r' : ℕ, IsLeast {l : ℕ | l.Prime ∧ ¬ l ∣ condE H * (H.pde - 1) * (H.pde' - 1)} r' ∧
      q0 ≡ 1 [MOD r' * condE H]) ∧
  H.levelPrimes = {H.g 0, H.g 1, H.pde, H.pde', q0}

def hostAt (H : Host R) (hc : H.ccK = ⊤) (u0 : R.A) (S : Finset ℕ) (hS : ∀ l ∈ S, Nat.Coprime l H.QS) : Host R :=
  { H with
    u0 := u0
    levelPrimes := H.levelPrimes ∪ S
    g_level := fun i => Finset.mem_union_left _ (H.g_level i)
    pde_level := ⟨Finset.mem_union_left _ H.pde_level.1, Finset.mem_union_left _ H.pde_level.2⟩
    ccK_coprime := fun p _ => by rw [hc, Ideal.absNorm_top]; exact Nat.coprime_one_left p
    level_coprimeS := fun p hp => (Finset.mem_union.1 hp).elim (H.level_coprimeS p) (hS p) }

theorem ArithData.ccK_eq {C : FC} {s : Scale} {H : Host R} {q0 : ℕ}
    {bs : R.A → R.A → R.A} (h : ArithData C s H q0 bs) : H.ccK = ⊤ := by
  have h1 := h.1
  unfold HostVal at h1
  casesm* _ ∧ _
  assumption

def bTop (C : FC) (s : Scale) (R : Ranks) : ℝ :=
  s.b' + 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (R.k : ℝ)

def numWords (C : FC) (s : Scale) (R : Ranks) : ℕ :=
  ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊

def Over {C : FC} (p : Pt C) (s : Scale) (H : Host R) (hc : H.ccK = ⊤)
    (bs : R.A → R.A → R.A) (a b : ℕ → ℤ)
    (code : Finset (Fin (R.k - 2) → Bool)) (off : ℕ → ℕ → ℝ) (u0 : R.A) (T : code → ℕ) : Prop :=
  (∃ hS : ∀ l ∈ Finset.univ.image T, Nat.Coprime l H.QS,
    (⟨p.D.R, p.D.host⟩ : Σ R' : Ranks, Host R') = ⟨R, hostAt H hc u0 (Finset.univ.image T) hS⟩) ∧
  p.L.sc = s ∧
  (∀ (h t : G.HH p.D) (h' t' : R.A), h.val = h'.val → t.val = t'.val →
    (p.ta.Gx.bs h t).val = (bs h' t').val) ∧
  (∀ (j : ℕ) (t : G.HH p.D), p.ta.Gx.off j (false, t) = off j t.val) ∧
  (∀ t : p.D.host.TT, p.L.aT t = a (t : p.D.R.A).val ∧ p.L.bT t = b (t : p.D.R.A).val) ∧
  ∃ e : p.D.what₂.Word ≃ code,
    (∀ u (l : Fin (R.k - 2)), wordBits p.D u l.1 = (e u).1 l) ∧ ∀ u, (p.D.mem u).A.T = T (e u)

def ObjectsExist (Q : PtProp) : Prop :=
  ∃ Cdg : ℝ, 0 < Cdg ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ C8 : ℝ, 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
      ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
        ∀ (R : Ranks), RankVal s R →
        ∀ (H : Host R) (q0 : ℕ) (bs : R.A → R.A → R.A)
          (hH : ArithData C s H q0 bs),
        ∀ a b : ℕ → ℤ, Win s R.k (H.TT.image Formalism.HC.Frame.A.val) (bTop C s R) a b →
        ∀ code : Finset (Fin (R.k - 2) → Bool), code.card = numWords C s R →
          ∃ off : ℕ → ℕ → ℝ, ∀ u0 : R.A, ∃ (T : code → ℕ) (p : Pt C),
            Over p s H hH.ccK_eq bs a b code off u0 T ∧
            (∀ u, p.L.AdmT u (p.D.mem u).A.T) ∧
            Val C cD ch p.L ∧ p.Has Q ∧ ChProviso_at p.L 3 ∧
            (∀ w, s.b ^ ((R.m : ℝ) / 2) ≤ (T w : ℝ) ∧ (T w : ℝ) ≤ s.b ^ (25 * (R.m : ℝ))) ∧
            FactDGam p.D Cdg

end GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ObjOnNarrowOfObjectsExist

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ObjExCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField GlobalTheory.EX GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

variable {R : Ranks}

theorem one_lt_condE (H : Host R) : 1 < condE H := by
  unfold condE
  exact lt_of_lt_of_le H.hyp.2.1.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))

theorem norm_modEq (H : Host R) (π : 𝓞 H.E) {T N : ℕ} (hN : N ≠ 0)
    (hn : (π : H.E) * H.conj (π : H.E) = (T : H.E)) (h1 : π - 1 ∈ Ideal.span {((N : ℕ) : 𝓞 H.E)}) :
    T ≡ 1 [MOD N] := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hyi : IsIntegral ℤ (a : H.E) := RingOfIntegers.isIntegral_coe a
  have hπ : (π : H.E) = 1 + N * (a : H.E) := by
    have := congrArg (fun z : 𝓞 H.E => (z : H.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    linear_combination -this
  have hci : IsIntegral ℤ (H.conj (a : H.E)) := hyi.map ((H.conj : H.E →+* H.E).toIntAlgHom)
  rw [hπ, map_add (f := _), map_mul, map_one, map_natCast] at hn
  set z : H.E := a + H.conj (a : H.E) + N * (a * H.conj (a : H.E)) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := H.E) N).mul (hyi.mul hci))
  have hM0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have h4 : z = algebraMap ℚ H.E (((T : ℚ) - 1) / N) := by
    have hM0' : (N : H.E) ≠ 0 := by exact_mod_cast hN
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff ] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((T : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : ℚ) = ((N * n : ℤ) : ℚ) := by
    have : (n : ℚ) = ((T : ℚ) - 1) / N := by simpa using hn'
    push_cast
    rw [this]
    field_simp
  exact (Nat.modEq_iff_dvd.2 ⟨n, by exact_mod_cast h5⟩).symm

theorem T_modEq (D : D7) (u : D.what₂.Word) : (D.mem u).A.T ≡ 1 [MOD condE D.host] := by
  obtain ⟨π, -, h2, h3⟩ := D.T_norm u
  have h0 : condE D.host * (D.host.g 0 * D.host.g 1) ^ 2 ≠ 0 :=
    Nat.mul_ne_zero (by have := one_lt_condE D.host; omega)
      (pow_ne_zero _ (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  exact (norm_modEq D.host π h0 h2 h3).of_mul_right _

end GlobalTheory.ObjExCompare

end
end
end
