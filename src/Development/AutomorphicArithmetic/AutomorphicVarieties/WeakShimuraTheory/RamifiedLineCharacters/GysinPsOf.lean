module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CoefFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.ExtRep
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.OpenKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.RootCharactersNeOneAtBasepoint
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SuppMMono
import Mathlib.FieldTheory.Galois.Profinite

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupRaw

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupRaw :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → Φ.Ok a → ∀ 𝒩 : Set Γ → Prop, Φ.Gys l 𝒩 → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ N', 𝒩 N' ∧ ∃ (x : Γ → k) (m : Φ.ι → k), (Φ.wN N').Coc a w x ∧ Φ.LocTriv a w x m ∧ (∃ g, a (Φ.rt w g) = 1 ∧ x g ≠ 0) ∧
        ∀ j, ∃ z, (Φ.wN N').Cup a w w' x (y j) z m := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ hfin hok 𝒩 hG w w' J _ y hy
  obtain ⟨M, i1, i2, i3, i4, i5, ρ, p, q, m0, hc, hN, hp, hq, hm0, hpm⟩ :=
    Gys.extRep Φ a l hfin hok.lc w w' J y hy
  obtain ⟨N', hN', c, hcZ, hc0, hloc, g, hg1, hcg, hspan⟩ :=
    hG M ρ hc (fun g hg => hN g (hok.kill g hg) (fun j => (hy j).kill g hg)) m0 hm0
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle ρ c).1 hcZ
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hcont
  have hrt : ∀ u, (Φ.wN N').rt u = Φ.rt u := fun u => rfl
  choose mm hmm using hloc
  have hpg : p (c g) ≠ 0 := hpm _ hspan hcg
  refine ⟨N', hN', fun s => p (c s), fun v => -p (mm v), ?_, ?_, ?_, ?_⟩
  · refine ⟨hlc.comp p, ?_, ?_⟩
    · intro s t
      rw [hrt, hcoc, map_add (f := _), hp]
    · intro s hs
      simp [hc0 s hs]
  · intro v s hs
    show p (c s) = -p (mm v) - a ↑((Φ.rt w) s) * -p (mm v)
    rw [hmm v s hs, map_sub, hp]
    ring
  · refine ⟨g, ?_, hpg⟩
    have h := hp g (c g)
    rw [hg1] at h
    change p (c g) = _ at h
    have h2 : (a ↑((Φ.rt w) g) - 1) * p (c g) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hpg
  · intro j
    refine ⟨fun s => q j (c s), hlc.comp (q j), ?_, ?_, ?_⟩
    · intro s t
      simp only [hrt]
      rw [hcoc, map_add (f := _), hq]
      ring
    · intro s hs
      simp [hc0 s hs]
    · intro v
      refine ⟨-q j (mm v), fun s hs => ?_⟩
      simp only [hrt]
      rw [hmm v s hs, map_sub, hq]
      ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupSwap

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupSwap :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (w w' : ℤ × ℤ) (x y z : Γ → R) (m n : Φ.ι → R), Φ.Coc a w x → Φ.LocTriv a w x m → Φ.Coc a w' y → Φ.LocTriv a w' y n →
      Φ.Cup a w w' x y z m → Φ.Cup a w' w y x (x * y - z) n := by
  intro O Γ R _ _ _ _ Φ a w w' x y z m n hx hm hy hn hz
  have e : ∀ g, a (Φ.rt (w + w') g) = a (Φ.rt w g) * a (Φ.rt w' g) := fun g => by
    rw [Fr.rt_add, Units.val_mul, map_mul]
  refine ⟨?_, fun g h => ?_, fun g hg => ?_, fun v => ?_⟩
  · exact (hx.lc.comp₂ hy.lc (· * ·)).comp₂ hz.lc (· - ·)
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, hx.coc, hy.coc, hz.coc, e]
    ring
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [hx.kill g hg, hz.kill g hg, zero_mul, sub_zero]
  · obtain ⟨o, ho⟩ := hz.loc v
    refine ⟨m v * n v - o, fun s hs => ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, ho s hs, e, hm v s hs, hn v s hs]
    ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.DataAl

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.dataAl :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (p : PD Φ.ι Γ R), Φ.IsRes a p → Supp nM p.r →
      ∃ x : Γ → R, Φ.Coc a (-wAl) x ∧ x Φ.g0 = 0 ∧ Φ.LocTriv a (-wAl) x (fun v => p.n v 1 0) ∧ ∀ g, p.r g 1 0 = x g * a (Φ.χ 0 g) := by
  intro O Γ R _ _ _ _ Φ a p hp hs
  have h12 : ∀ g, p.r g 1 2 = 0 := fun g => hs g 1 2 (by decide) (by decide)
  have h13 : ∀ g, p.r g 1 3 = 0 := fun g => hs g 1 3 (by decide) (by decide)
  have hd := hp.res.diag
  have hu : ∀ g, a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) * a (Φ.χ 0 g) = 1 := fun g => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hrt : ∀ g, a (Φ.rt (-wAl) g) = a (Φ.χ 1 g) * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) := fun g => by
    rw [← map_mul, ← Units.val_mul]
    congr 2
    simp [Fr.rt, wAl]
  have hlc : ∀ i j, IsLocallyConstant fun g => p.r g i j := fun i j => by
    refine IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (hp.cont i j 1) ?_
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]
  refine ⟨fun g => p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine (hlc 1 0).mul ?_
    have e : (fun g => a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) = Ring.inverse ∘ fun g => p.r g 0 0 := by
      funext g
      simp only [Function.comp, hd]
      exact (Ring.inverse_unit (Units.map (a : O →* R) (Φ.χ 0 g))).symm
    rw [e]
    exact (hlc 0 0).comp _
  · intro g h
    have e : p.r (g * h) 1 0 = p.r g 1 0 * a (Φ.χ 0 h) + a (Φ.χ 1 g) * p.r h 1 0 := by
      rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, h12, h13, hd, hd]; ring
    rw [e, hrt, map_mul, mul_inv, Units.val_mul, map_mul]
    linear_combination (p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) * hu h
  · intro g hg
    simp [hp.pair.kill g hg]
  · have : p.r Φ.g0 1 0 = 0 := hp.pair.nrm (by decide)
    simp [this]
  · intro v s hsv
    obtain ⟨l1, l2, l3⟩ := hp.pair.low v
    have hinv : p.n v * adj (p.n v) = 1 := by
      rw [IsGSp, one_smul] at l1
      exact mul_eq_one_comm.mp l1
    have hU := hp.pair.flag v s hsv
    have hc := hp.res.char v s hsv 0
    unfold PD.ψ at hc
    have key : p.n v * (adj (p.n v) * p.r s * p.n v) = p.r s * p.n v := by
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    generalize adj (p.n v) * p.r s * p.n v = U at hU hc key
    have k := congrFun (congrFun key 1) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four, hU 1 0 (by decide), hU 2 0 (by decide),
      hU 3 0 (by decide), hc, h12, h13, hd, l2, l2] at k
    rw [hrt]
    beta_reduce
    linear_combination (-a (((Φ.χ 0 s)⁻¹ : Oˣ) : O)) * k + p.n v 1 0 * hu s
  · intro g
    beta_reduce
    rw [mul_assoc, hu, mul_one]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GysinPsOf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupEx (P : CohomologyHyp) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (T : Tower D) (hT : T.Fit) (k : Type) [Field k] (a : c.O →+* k) (ha : ∀ x ∈ maximalIdeal c.O, a x = 0)
    (W : Finset ℕ) (hW : ∀ w ∈ W, w.Prime ∧ T.Splits w) (w w' : ℤ × ℤ) (h1 : a ((T.fr W).rt w T.g0) ≠ 1)
    (h2 : a ((T.fr W).rt (w + w') T.g0) ≠ 1) (J : Type) [Finite J] (y : J → G T.F Ω → k)
    (hy : ∀ j, (T.fr W).Coc a w' (y j) ∧ y j T.g0 = 0) :
    ∃ W' : Finset ℕ, W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (∀ j, (T.fr W').Coc a w' (y j)) ∧
      ∃ (x : G T.F Ω → k) (m : T.ι → k), (T.fr W').Coc a w x ∧ x T.g0 = 0 ∧ (T.fr W').LocTriv a w x m ∧ (∃ g, x g ≠ 0) ∧
        ∀ j, ∃ z, (T.fr W').Cup a w w' x (y j) z m ∧ z T.g0 = 0 := by
  obtain ⟨hc, hf⟩ := Gys.coefFacts c k a ha
  have hD : D.Good := hT.2.elim (fun h => h.1.1) fun h => h.1.1
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨N', hN, x, m, hx, hm, ⟨g, g1, g2⟩, hz⟩ := Gys.cupRaw (T.fr W) a l hf (ok W) _ (Gys.gysT P D T hD W hW) w w' J y
    fun j => (hy j).1
  have hs := hN.sub
  obtain ⟨W', s1, s2, rfl⟩ := hN
  have hy' : ∀ j, (T.fr W').Coc a w' (y j) := fun j => ⟨(hy j).1.lc, (hy j).1.coc, fun g hg => (hy j).1.kill g (hs hg)⟩
  obtain ⟨x', m', b1, b2, b3, b4, b5⟩ := Gys.cupNorm (T.fr W') a (ok W') w w' h1 h2 J y (fun j => ⟨hy' j, (hy j).2⟩) x m hx hm hz
  exact ⟨W', s1, s2, hy', x', m', b1, b2, b3, ⟨g, (b4 g g1).symm ▸ g2⟩, b5⟩

theorem UpperTheory.V.Ws.Gys.mu_of {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R)
    {p : PD Φ.ι Γ R} (hp : Φ.IsRes a p) (h : ∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) :
    ∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v ∧ ∀ i, a (Φ.χ i s) = 1 :=
  fun v s hs => ⟨h v s hs, fun i => (hp.res.char v s (h v s hs) i).symm.trans (hp.pair.mu v s hs i)⟩

theorem UpperTheory.V.Ws.Gys.gysinPs_of :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → Supp nM p.r →
      ∃ (W' : Finset ℕ) (s : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ s.In qQ ∧ s.SameAl p ∧ Ent s.r (-wPs) := by
  intro P Ω _ _ _ l _ c D T hT k _ a ha W hW p hp hs
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨-, r2, r3⟩ := Gys.rootCharacters_ne_one_at_basepoint (T.fr W) a (ok W)
  obtain ⟨x, x1, x2, x3, x4⟩ := Gys.dataAl (T.fr W) a p hp hs
  obtain ⟨W', s1, s2, hx, y, n, y1, y2, y3, ⟨g, hg⟩, hz⟩ := Gys.cupEx P D T hT k a ha W hW (-wPs) (-wAl) r2
    (by rw [add_comm]; exact r3) Unit (fun _ => x) fun _ => ⟨x1, x2⟩
  obtain ⟨z, z1, z2⟩ := hz ()
  have hmu := Gys.mu_of (T.fr W) a hp fun v s hs => hs.1
  obtain ⟨s, a1, a2, a3, a4, a5, -⟩ := Gys.ob (T.fr W') a (ok W') hmu x y (y * x - z) _ n (hx ()) x2 x3 y1 y2 y3
    (Gys.cupSwap (T.fr W') a _ _ y x z n _ y1 y3 (hx ()) x3 z1) (by
      show y T.g0 * x T.g0 - z T.g0 = 0
      rw [y2, z2, zero_mul, sub_zero])
  exact ⟨W', s, s1, s2, a1, a2, ⟨fun g => (a3 g).trans (x4 g).symm, a4⟩, g, 2, 0, by decide,
    a5 g ▸ mul_ne_zero hg (((T.fr W').χ 0 g).isUnit.map a).ne_zero⟩
end
end
