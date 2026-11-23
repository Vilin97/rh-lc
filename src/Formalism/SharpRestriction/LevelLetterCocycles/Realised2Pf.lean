module

public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingEveryOrdering
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Formalism.SharpRestriction.LevelLetterCocycles.ExponentWindowSubsetShort
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfAssemble
public import Formalism.SharpRestriction.LevelLetterCocycles.TeichOnto
import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ExpRescaleCoeff

section

@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem expRescale_coeff (S : Type) [CommRing S] [Algebra ℚ S] (E : PowerSeries S)
    (h0 : constantCoeff E = 1) (hd : PowerSeries.derivative E = E) (n : ℕ) :
    coeff n E = algebraMap ℚ S (1 / (n.factorial : ℚ)) := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have h := congrArg (coeff n) hd
    rw [PowerSeries.coeff_derivative, ih] at h
    have hn : ((n : S) + 1) = algebraMap ℚ S ((n : ℚ) + 1) := by simp
    rw [hn] at h
    have hu : coeff (n + 1) E =
        coeff (n + 1) E * algebraMap ℚ S ((n : ℚ) + 1) * algebraMap ℚ S (1 / ((n : ℚ) + 1)) := by
      rw [mul_assoc, ← map_mul, mul_one_div_cancel (by positivity), map_one, mul_one]
    rw [hu, h, ← map_mul, Nat.factorial_succ]
    congr 1
    push_cast
    field_simp

theorem expRescale : ExpRescaleStatement := by
  intro S _ _ E h0 hd
  have hE : E = PowerSeries.exp S := by
    ext n
    rw [expRescale_coeff S E h0 hd n, PowerSeries.coeff_exp]
  refine ⟨hE, fun a => ?_⟩
  rw [hE, PowerSeries.exp_pow_eq_rescale_exp]

end LevelStatements.Lv
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicFrobeniusPowerSeriesX

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem cyclotomicFrobeniusPowerSeries_X (W : LocWach PD LL O v n) : W.φ₀ X = (1 + X) ^ PD.p - 1 := by
  rw [W.φ₀_X, W.q₀_def]

theorem cyclo_comp_mul_X {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] :
    (Polynomial.cyclotomic p R).comp (Polynomial.X + 1) * Polynomial.X =
      (Polynomial.X + 1) ^ p - 1 := by
  rw [Polynomial.cyclotomic_prime]
  have hc : (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial R) ^ i).comp (Polynomial.X + 1) =
      ∑ i ∈ Finset.range p, (Polynomial.X + 1) ^ i := by
    simp [Polynomial.comp, Polynomial.eval₂_finsetSum]
  have h := geom_sum_mul (Polynomial.X + 1 : Polynomial R) p
  rw [add_sub_cancel_right] at h
  rw [hc, h]

theorem glue2 [IsDomain O] (hR : Ring9 W) :
    ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have h0 := congrFun hw 0
  have hq : (baseIdOf hR).ι (baseIdOf hR).Bs.q = W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O) := by
    change (baseIdOf hR).ι (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = _
    rw [map_add (f := _), (baseIdOf hR).ι_X]
    congr 1
    exact (baseIdOf hR).ι.commutes _
  have hcyc : (W.q₀ : PowerSeries O) =
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) := by
    have hX : (PowerSeries.X : PowerSeries O) ≠ 0 := PowerSeries.X_ne_zero
    apply mul_left_cancel₀ hX
    rw [W.q₀_def]
    have := congrArg (fun f : Polynomial O => (f : PowerSeries O)) (cyclo_comp_mul_X (R := O) PD.p)
    simp only [Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_add, Polynomial.coe_one] at this
    rw [mul_comm, this, add_comm]
  have h0' : W.q₀ = (w : LetA O n) 0 * (W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O)) := by
    simpa [LocWach.q, Formalism.MainNotions.DeltaInvariantLattices.Eat, LocWach.π₀, Polynomial.aeval_add, Polynomial.aeval_X,
      Polynomial.aeval_C] using h0
  let w0 : (PowerSeries O)ˣ := Units.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) 0) w
  refine ⟨w0⁻¹, ?_⟩
  rw [hq, ← hcyc, h0']
  change _ = ((w0⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) * ((w0 : PowerSeries O) * _)
  rw [← mul_assoc, Units.inv_mul, one_mul]

theorem rhoZ_exp [CharZero LL] (c : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    1 + rhoZ W c ζ X = PowerSeries.C ζ * exp LL := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π c ζ hζ
  have hE := (LevelStatements.Lv.expRescale LL E h0 h1).1
  rw [← hE, ← h2]
  rfl

end Formalism.MainNotions.N.Ln03
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfArcChoices

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.MainNotions.WachCoordinates

theorem hn_of {n j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hCu : CutsOK n j ty cuts arcLen) {c : ZMod n} (hc : c ∈ (cutsOf hCu).cuts) :
    (cutsOf hCu).ell c ≤ n :=
  (cutsOf hCu).ell_le c hc

theorem hj_of {n j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hCu : CutsOK n j ty cuts arcLen) {c : ZMod n} (hc : c ∈ (cutsOf hCu).cuts) :
    j ≤ (cutsOf hCu).ell c := by
  simp only [Formalism.MainNotions.WachCoordinates.cutsOf_cuts] at hc
  simp only [Formalism.MainNotions.WachCoordinates.cutsOf_ell]
  exact hCu.2.2.2.1 c hc

theorem three_g_le_parameter_bound {l : ℕ} (hl : 2 ≤ l) {G S η h : ℕ} (hg : gPar G S η ≤ h) :
    3 * gPar G S η ≤ (l - 1) * Formalism.ExponentWindows.E.parM l h (gPar G S η) := by
  unfold Formalism.ExponentWindows.E.parM
  have hd : 0 < l - 1 := by omega
  have h1 := Nat.lt_mul_div_succ (h + 2 * gPar G S η) hd
  exact le_of_lt (lt_of_le_of_lt (by omega) h1)

end Formalism.MainNotions.N.Ln03.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfTeichOnto

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.MainNotions.N.Ln03 Polynomial

theorem teichOnto_toZMod_eq_zero_iff {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← PadicInt.mem_nonunits, mem_nonunits_iff]

theorem teichOnto_norm_eq_one {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) (h : PadicInt.toZMod x ≠ 0) :
    ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one x) (not_lt.mp fun h' => h ((teichOnto_toZMod_eq_zero_iff x).mpr h'))

theorem teichOnto_holds (p : ℕ) [Fact p.Prime] : TeichOnto p := by
  intro a ha
  have hp : p.Prime := Fact.out
  set a₀ : ℤ_[p] := ((a.val : ℕ) : ℤ_[p]) with ha₀
  have hres : PadicInt.toZMod a₀ = a := by rw [ha₀, map_natCast, ZMod.natCast_zmod_val]
  set F : Polynomial ℤ_[p] := X ^ (p - 1) - 1 with hF
  have hFa : F.aeval a₀ = a₀ ^ (p - 1) - 1 := by simp [hF]
  have hF'a : F.derivative.aeval a₀ = ((p - 1 : ℕ) : ℤ_[p]) * a₀ ^ (p - 1 - 1) := by
    simp [hF, Polynomial.derivative_X_pow]
  have h1 : ‖F.aeval a₀‖ < 1 := by
    rw [← teichOnto_toZMod_eq_zero_iff, hFa, map_sub, map_pow, hres, map_one,
      ZMod.pow_card_sub_one_eq_one ha, sub_self]
  have h2 : ‖F.derivative.aeval a₀‖ = 1 := by
    apply teichOnto_norm_eq_one
    rw [hF'a, map_mul, map_pow, hres, map_natCast]
    refine mul_ne_zero ?_ (pow_ne_zero _ ha)
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, neg_ne_zero]
    exact one_ne_zero
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a₀) (by rw [h2, one_pow]; exact h1)
  rw [h2] at hza
  have hzp : z ^ (p - 1) = 1 := by
    have : F.aeval z = z ^ (p - 1) - 1 := by simp [hF]
    rw [this, sub_eq_zero] at hz
    exact hz
  have hzz : z * z ^ (p - 2) = 1 := by
    have h2p := hp.two_le
    rw [← pow_succ', show p - 2 + 1 = p - 1 by omega, hzp]
  let u : ℤ_[p]ˣ := ⟨z, z ^ (p - 2), hzz, by rw [mul_comm]; exact hzz⟩
  refine ⟨⟨u, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hzp)⟩, ?_⟩
  show PadicInt.toZMod z = a
  have h3 : PadicInt.toZMod (z - a₀) = 0 := (teichOnto_toZMod_eq_zero_iff _).mpr hza
  rw [map_sub, sub_eq_zero, hres] at h3
  exact h3

end Formalism.MainNotions.N.Ln03.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.Realised2Pf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows IsLocalRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem basis_of {I : BaseId W} {T : LocLat G Qp LL O} (hInj : I.Inj) (hFull : I.Full)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (C : Coord W I T) (i : ZMod n) :
    ∃ (r : ℕ) (e : Fin r → C.V) (b : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i)),
      ∀ k, (b k : C.V) = e k := by
  obtain ⟨r, e, hli, hsp⟩ := free_of hInj hFull hmod C i
  refine ⟨r, e, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp), fun k => ?_⟩
  simp [Module.Basis.span_apply]

theorem matrix_of {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] {N₂ : Submodule (PowerSeries O) V₂} {r₁ r₂ : ℕ} (f : V₁ → V₂)
    (e₁ : Fin r₁ → V₁) (e₂ : Fin r₂ → V₂) (b₂ : Module.Basis (Fin r₂) (PowerSeries O) ↥N₂)
    (hb₂ : ∀ k, (b₂ k : V₂) = e₂ k) (hf : ∀ k, f (e₁ k) ∈ N₂) :
    ∃ P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O), ∀ k, ∃ a : Fin r₂ → PowerSeries O,
      f (e₁ k) = ∑ l, a l • e₂ l ∧ ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l) := by
  refine ⟨Matrix.toLin' (Matrix.of fun l k => PowerSeries.constantCoeff (b₂.repr ⟨_, hf k⟩ l)),
    fun k => ⟨fun l => b₂.repr ⟨_, hf k⟩ l, ?_, fun l => by simp⟩⟩
  have h := b₂.sum_repr ⟨_, hf k⟩
  have h' := congrArg (fun x : ↥N₂ => (x : V₂)) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, hb₂] at h'
  exact h'.symm

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero LL]
  [IsFractionRing O LL] [Fintype (K →ₐ[Qp] LL)]

theorem realised2_pf (Lb : LevB W) (hR : Ring9 W) (e : W.DD W.one) (uZ : ℤ_[PD.p]ˣ)
    (ιZ : ℤ_[PD.p] →+* O)
    (hLevN : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hCmp : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T)),
      W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)
    (hLevBφ : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL),
      (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) • φVB PD (LL := LL) (V := T.V)
            (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (hLevBΓ : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL)
      (j a : ℕ), IsPrimitiveRoot ζ (PD.p ^ j) →
      (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) → ζ' = ζ ^ a →
      ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hLevΓ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ), IsPrimitiveRoot ζ (PD.p ^ j) →
      (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) → ζ' = ζ ^ a →
      ∀ f : LetA O n, W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hLevφ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hs : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hP4Lev : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W) (hDdR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hHod : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ →
      F.Onto → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    (hV : ValRing O v) (hK : Function.Bijective (algebraMap K₀ K))
    (hpm : (PD.p : O) ∈ maximalIdeal O) (hrich : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (huZ : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (he : UnitGen W e) (hone : IsCrys PD W.one.ρ) (h5 : 5 ≤ PD.p) : Realised2 hR e := by
  intro T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen hCu hKJ hJ hg hS hT
  obtain ⟨C₁, C₂, C₀, hC, e₀, he₀⟩ :=
    Formalism.MainNotions.N.Ln03.Pf.coordSteps_holds hR hs hP9 hLem3 hDdR he hone hK h5 T₁ T₂ F hc₁ hc₂ hon
  refine ⟨{ C₁ := C₁, C₂ := C₂, C₀ := C₀, h := hC, e₀ := e₀, Ks := KsW W, Δ := DeltaT PD.p },
    { he₀ := he₀, arcs := fun ϖ hϖ c hc => ?_ }⟩
  have hp2 : PD.p ≠ 2 := by omega
  have hp9 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ := fun T hT =>
    ((hP9 T hT hs hp2).2.2 (unram_of hK)).2
  obtain ⟨r₁, e₁, b₁, hb₁⟩ := basis_of (baseIdOf_inj hR) (baseIdOf_full hR) (hp9 T₁ hc₁.2.2.2) C₁
    (c - ((cutsOf hCu).ell c : ZMod n))
  obtain ⟨r₂, e₂, b₂, hb₂⟩ := basis_of (baseIdOf_inj hR) (baseIdOf_full hR) (hp9 T₂ hc₂.2.2.2) C₂
    (c - ((cutsOf hCu).ell c : ZMod n))
  obtain ⟨P, hP⟩ := matrix_of (latHomOf hC).f e₁ e₂ b₂ hb₂ (fun k =>
    (latHomOf hC).map_N _ _ (by rw [← hb₁ k]; exact (b₁ k).2))
  exact Formalism.MainNotions.N.Ln03.Pf.finalArc_holds Lb uZ ιZ hC c _ _ ϖ j _ _ Gp S η ty e₁ e₂ P hLevN hCmp hLevBφ
    hLevBΓ hLevΓ hLevφ hs hP4 hP4Lev hSat hP3 hP9 hP5 hDdR hHod hc₁ hc₂ hon hKJ hV hK hϖ hpm
    (Formalism.MainNotions.N.Ln03.Pf.hn_of hCu hc) hrich (glue2 hR) (cyclotomicFrobeniusPowerSeries_X W)
    (fun s _ ζ hζ => rhoZ_exp c ζ ⟨s + 1, (mem_primitiveRoots (pow_pos PD.hp.pos _)).1 hζ⟩)
    huZ hutie (Formalism.MainNotions.N.Ln03.Pf.teichOnto_holds PD.p) h5 b₁ hb₁ b₂ hb₂ hP
    (Formalism.MainNotions.N.Ln03.Pf.hj_of hCu hc) (Formalism.MainNotions.N.Ln03.Pf.three_g_le_parameter_bound PD.hp.two_le hg)

end Formalism.MainNotions.N.Ln03
end
end
end
