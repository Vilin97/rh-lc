module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralFourierCoeffClassIndicatorLevelPoint
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesBoundCoprimeTorsionMulStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardFunLevQ
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfCastDvd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TotalDegreeLeOfRowDeg
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRule

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectedLatticeDetIdealTypeNormIntegral

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LatticeIndex

theorem intersected_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.LevOK N M → ℓ.Prime → ∀ (A : GlobalTheory.PlaceInt.Adapt Λ N ℓ) (s : c.F), Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → ∀ e : ℕ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) := by
  intro E _ _ _ H Dw l c n Λ N M ℓ hL hl A s hs T io hu e
  have hN : N ≠ 0 := by rintro rfl; exact absurd hL.1 (by decide)
  let w := (valV (K' := T.Fr) T.V).comap io
  have hwi : ∀ x : c.F, IsIntegral ℤ x → w x ≤ 1 := fun x hx => valV_integral T
    (by convert map_isIntegral_int io hx; exact Subsingleton.elim _ _)
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => hwi _ r.isIntegral_coe
  have hwτ : ∀ τ, ∀ r : 𝓞 E, w.comap (embF c τ) (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    hwi _ (map_isIntegral_int (embF c τ) r.isIntegral_coe)
  have hnat : ∀ τ (k : ℕ), Nat.Coprime k ℓ → w.comap (embF c τ) (k : E) = 1 := fun τ k hk => by
    simp only [w, Valuation.comap_apply, map_natCast]
    exact valV_nat T hk hu
  have hn : ∀ τ, HasMax w (idealAt c Λ.Ln τ) (w.comap (embF c τ) (algebraMap (𝓞 E) E A.g.det)) := fun τ => by
    obtain ⟨a, b⟩ := detSet_Ln A _ (hwτ τ) (hnat τ _ A.cop₁)
    refine hasMax_span hw ?_ ⟨_, ⟨_, b, rfl⟩, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    exact a y hy
  have ha : ∀ τ, HasMax w (idealAt c Λ.La τ) (w.comap (embF c τ) A.ga.det)⁻¹ := fun τ => by
    obtain ⟨-, a, y, hy, b⟩ := detSet_La A _ (hwτ τ) (hnat τ _ A.cop)
    refine hasMax_span hw ?_ ⟨_, ⟨_, hy, rfl⟩, b⟩
    rintro _ ⟨y, hy, rfl⟩
    exact a y hy
  have h0 : ∀ τ, w.comap (embF c τ) A.ga.det ≠ 0 := fun τ => (detSet_La A _ (hwτ τ) (hnat τ _ A.cop)).1
  have hp : ∀ τ, w (embK c τ A.p.det) * (w.comap (embF c τ) A.ga.det)⁻¹ =
      w.comap (embF c τ) (algebraMap (𝓞 E) E A.g.det) := fun τ => by
    have := congrArg (w.comap (embF c τ)) (det_p A hN)
    simp only [map_mul, map_pow, hnat τ _ A.cop, hnat τ _ A.cop₁, _root_.one_pow, _root_.mul_one, _root_.one_mul] at this
    rw [mul_inv_eq_iff_eq_mul₀ (h0 τ), mul_comm]
    exact this
  have hb : HasMax w (Submodule.span (𝓞 c.F) {s}) (w s) := hasMax_span hw (by simp) (by simp)
  have e1 := hb.mul (hasMax_prod hw Finset.univ _ _ fun τ => (hn τ).pow hw (Dw.mult τ))
  have e2 := hasMax_prod hw Finset.univ _ _ fun τ => (ha τ).pow hw (Dw.mult τ)
  obtain ⟨y, hy, hyv⟩ := e1.2
  have hle := e2.1 y (hs hy)
  rw [hyv] at hle
  simp only [← hp, mul_pow, Finset.prod_mul_distrib, ← _root_.mul_assoc] at hle
  have hpos : 0 < ∏ τ : E →+* ℂ, (w.comap (embF c τ) A.ga.det)⁻¹ ^ Dw.mult τ :=
    zero_lt_iff.2 (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (inv_ne_zero (h0 τ)))
  have hw1 : w (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) ≤ 1 := by
    rw [map_mul, map_prod]
    simp only [map_pow]
    refine le_of_mul_le_mul_right ?_ hpos
    rw [_root_.one_mul]
    exact hle
  have hv : valV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) ≤ 1 := hw1
  by_cases hx : io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) = 0
  · rw [hx, nval_zero]; exact le_top
  rw [nval_of_ne hx]
  have hlog : WithZero.log (valV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ))) ≤ 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_le_log (valV_ne_zero hx) one_ne_zero).2 hv
  have h0v : (0 : ℝ) ≤ (vV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) : ℝ) := by
    simp only [vV]; exact_mod_cast (by omega)
  exact EReal.coe_nonneg.2 (div_nonneg h0v (Nat.cast_nonneg _))

end GlobalTheory.LatticeIndex
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectedLatticeDetIdealTypeNormIntegralStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section


theorem _root_.GlobalTheory.T.intersectedLattice_detIdeal_typeNorm_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.LevOK N M → ℓ.Prime → ∀ (A : GlobalTheory.PlaceInt.Adapt Λ N ℓ) (s : c.F), Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → ∀ e : ℕ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) := by
  first | exact @GlobalTheory.LatticeIndex.intersected_integral | exact GlobalTheory.LatticeIndex.intersected_integral | (intros; apply GlobalTheory.LatticeIndex.intersected_integral <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearingIntegerShortSeriesIntegralCoprimeLevel

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat GlobalTheory.ShortBound
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovInt



theorem smul_intZ_nonneg_coprime : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ →
    (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) →
    (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 →
    ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M →
    ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w →
    ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g →
    ∀ la : HeightOneSpectrum (𝓞 c.F), (∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ¬ ℓ ∣ d.l₂.M) →
    ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤
      ∏ τ : D.host.E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ →
    ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((s * betaH (Dw := Dw) c Λ * (intZ D Dw d.l₂ n w : c.F)) • g) := by
  intro D H Dw l Xo c n d _ hlev hnab hroot hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la hla s hs v hv
  have hroot1 : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k),
      evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1 := fun k _ _ y₂ => by rw [pow_one]; exact hroot k y₂
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    exacts [h.choose_spec.1, one_ne_zero]
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ, P₀ = (NumberField.discr D.host.E).natAbs := ⟨_, rfl⟩
  have hP0 : P₀ ≠ 0 := hP₀ ▸ Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = P₀ ^ Formalism.L2.Pj.DF Dw w * d.l₂.M ^ Formalism.L2.Pj.DF Dw w *
    Nat.card (Fin n → LevQ Dw d.l₂) := ⟨_, rfl⟩
  have hK0 : K ≠ 0 := hK ▸ mul_ne_zero (mul_ne_zero (pow_ne_zero _ hP0) (pow_ne_zero _ hM0)) hc0
  have hKZ : intZ D Dw d.l₂ n w = K := by rw [intZ, hK, hP₀]; ring
  rw [hKZ, mul_comm]
  obtain ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩ := hv
  show 0 ≤ nval Tc.V e (evI yI _)
  rw [evI_smul]
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot1 Λ N hU hTM hN w P hP x0 g hsec hR
      Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have heR : (0 : ℝ) < ((r * e : ℕ) : ℝ) := by exact_mod_cast he'
  rw [← nval_bc iT hr hiT e, map_mul, hval, ← hio]
  obtain ⟨ℓ, hℓ, hu⟩ := GlobalTheory.ShortBound.exists_resChar T' hfr
  have hmem : (ℓ : 𝓞 c.F) ∈ la.asIdeal := by
    by_contra hnm
    have h2 := ho'.2 (ℓ : c.F)
    have hv1 : la.valuation c.F (ℓ : c.F) = 1 := by
      rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
      exact la.valuation_eq_one_iff_notMem.2 hnm
    have hv0 : vLa la (ℓ : c.F) = 0 := by simp [vLa, hv1]
    rw [map_natCast, hv0, mul_zero] at h2
    have h0 : (ℓ : T'.V) ≠ 0 := fun h0 => by
      have : algebraMap T'.V T'.Fr (ℓ : T'.V) = 0 := by rw [h0, map_zero]
      rw [map_natCast] at this
      exact hℓ.ne_zero (by exact_mod_cast this)
    have h3 := GlobalTheory.PlaceExtField.vV_pos (K' := T'.Fr) h0 hu
    rw [map_natCast] at h3
    omega
  have hd : ¬ ℓ ∣ d.l₂.M := hla ℓ hℓ hmem
  obtain ⟨α, hα1⟩ : ∃ α : ℕ, α = 1 := ⟨1, rfl⟩
  obtain ⟨α', hα'⟩ : ∃ α' : ℕ, d.l₂.M = α * α' := ⟨d.l₂.M, by rw [hα1, Nat.one_mul]⟩
  have ha0 : α ≠ 0 := by rw [hα1]; exact one_ne_zero
  have ha0' : α' ≠ 0 := right_ne_zero_of_mul (hα' ▸ hM0)
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  haveI := Nat.finite_of_card_ne_zero hc0
  have hu0 : io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) ≠ 0 :=
    (map_ne_zero io₂).2 (nrm_ne_zero _ _ (Nat.cast_ne_zero.2 ha0))
  have hsA : ∀ A : GlobalTheory.PlaceInt.Adapt Λ N ℓ, 0 ≤ nval T'.V (r * e)
      (io₂ (d.eF s * ∏ τ : D.host.E →+* ℂ, embK d.c₂ τ A.p.det ^ Dw.mult τ)) := by
    intro A
    have h := GlobalTheory.T.intersectedLattice_detIdeal_typeNorm_integral D.host.E H Dw l c n Λ N d.l₂.M ℓ hN hℓ A s hs T'
      (io₂.comp (d.eF : c.F →+* d.c₂.F)) hu (r * e)
    simpa [embK, map_prod, map_pow, GlobalTheory.PlaceInt.eF_embF] using h
  obtain ⟨t1, -⟩ := GlobalTheory.TorsFac.factorisation D.host.E H Dw d.l₂ d.Xo₂ N ℓ hN.1 hN.2.1 hℓ
  obtain ⟨n', j, -, -, h5⟩ := t1 hd
  have hcop : ∀ q, ∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp q b ^ m = 1 := fun q => by
    have hk : ∀ b, KilledBy d.Xo₂ d.l₂.Mb (tp q b ^ N) := fun b => by
      rw [(htp q b).1]; exact levPt_killed d.Xo₂ _ _
    choose i hi using fun b => (h5 _ _ (hk b) (htp q b).2).2.2
    refine ⟨d.l₂.M ^ (∑ b, i b), Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd).symm, fun b => ?_⟩
    obtain ⟨m, hm⟩ : d.l₂.M ^ i b ∣ d.l₂.M ^ (∑ b, i b) :=
      pow_dvd_pow _ (Finset.single_le_sum (f := i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
    rw [hm, pow_mul, hi b, one_pow]
  have hN2 : ∀ q b, tp q b ^ (N ^ 2) = 1 := fun q b => by
    have hk : KilledBy d.Xo₂ d.l₂.Mb (tp q b ^ N) := by rw [(htp q b).1]; exact levPt_killed d.Xo₂ _ _
    exact (h5 _ _ hk (htp q b).2).1
  have hterm := fun q => GlobalTheory.T.shortSeries_bound_coprime_torsion_mul D.host.E H Dw d.l₂ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he'
    hch ℓ hℓ hu Λ N d.l₂.M hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (hN2 q) (hF q) hrat (hcop q) (d.eF s) hsA
  have hX1 : ∀ {J : Type} (bb : T'.Fr) (X : J → T'.Fr) (ρ : ℝ),
      (∀ q, ((-ρ : ℝ) : EReal) ≤ nval T'.V (r * e) (bb * X q)) →
      ∀ q, ((-ρ : ℝ) : EReal) ≤ nval T'.V (r * e) (io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) * bb * X q) := by
    intro J bb X ρ h q
    rw [hα1, Nat.cast_one, nrm_one, map_one, _root_.one_mul]
    exact h q
  have key := le_nval_avg (V := T'.V) (r * e) (fun q => io₂ (d.w x0 q)) _ ζ _
    ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) _ 1 one_pos hζ hu0 (by exact_mod_cast hc0)
    (fun q => map_isIntegral_int io₂ (hwi x0 q)) _ (hX1 _ _ _ hterm)
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hKv := add_le_add (le_refl (nval T'.V (r * e) (K : T'.Fr))) key
  rw [← nval_mul, nval_of_ne (Nat.cast_ne_zero.2 hK0), ← EReal.coe_add] at hKv
  refine le_trans (EReal.coe_nonneg.2 ?_) (hKv.trans (le_of_eq ?_))
  · have b0 : ∀ p : ℕ, (0 : ℝ) ≤ vV T'.V (p : T'.Fr) := fun p => by
      exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p
    have b1 : (vV T'.V (K : T'.Fr) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) +
        (Formalism.L2.Pj.DF Dw w : ℕ) * ((vV T'.V (α : T'.Fr) : ℝ) + vV T'.V (α' : T'.Fr)) +
        vV T'.V ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) := by
      rw [hK, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        vV_mul (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)))
          (Nat.cast_ne_zero.2 hc0),
        vV_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)),
        vV_pow (Nat.cast_ne_zero.2 hP0), vV_pow (Nat.cast_ne_zero.2 hM0)]
      conv_lhs => rw [show ((d.l₂.M : ℕ) : T'.Fr) = (α : T'.Fr) * (α' : T'.Fr) by rw [hα', Nat.cast_mul],
        vV_mul (Nat.cast_ne_zero.2 ha0) (Nat.cast_ne_zero.2 ha0')]
      push_cast
      ring
    have b2 : (vV T'.V (io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E))) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * vV T'.V (α : T'.Fr) := by
      rw [nrm_nat, map_pow, map_natCast, vV_pow (Nat.cast_ne_zero.2 ha0)]
      push_cast
      ring
    have b3 : ∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) *
        D.host.vdH p * (Formalism.L2.Pj.DF Dw w : ℝ) / 2 ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) / (r * e : ℕ) := by
      have h := ram_sum_le_vV_discr D.host.E T' _ (fun p (hp : p ∈ D.host.condN.primeFactors) => Nat.prime_of_mem_primeFactors hp)
        (r * e) (Formalism.L2.Pj.DF Dw w)
      rw [Nat.cast_pow, vV_pow (Nat.cast_ne_zero.2 (hP₀ ▸ hP0)), Int.cast_mul, Int.cast_natCast] at h
      rw [hP₀]
      exact h
    have b4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (α' : T'.Fr) : ℝ) / (r * e : ℕ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (b0 _)) heR.le
    rw [b1, b2, add_div, add_div, mul_add, add_div]
    linarith
  · congr 1
    simp only [map_mul, map_inv₀, map_natCast]
    field_simp

end GlobalTheory.CovInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearingIntegerShortSeriesIntegralCoprimeLevelStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat GlobalTheory.ShortBound
set_option autoImplicit false

noncomputable section


theorem _root_.GlobalTheory.T.clearingInteger_shortSeries_integral_coprimeLevel : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ → (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) → (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 → ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g → ∀ la : HeightOneSpectrum (𝓞 c.F), (∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ¬ ℓ ∣ d.l₂.M) → ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((s * betaH (Dw := Dw) c Λ * (intZ D Dw d.l₂ n w : c.F)) • g) := by
  first | exact @GlobalTheory.CovInt.smul_intZ_nonneg_coprime | exact GlobalTheory.CovInt.smul_intZ_nonneg_coprime | (intros; apply GlobalTheory.CovInt.smul_intZ_nonneg_coprime <;> assumption)
end
end
end
