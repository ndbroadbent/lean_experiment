# FORMAL VERIFICATION: The Sky Is Blue

> *"It's like trying to prove 'the sky is blue' in a theorem prover - the formal system talks about syntax, not the physical world"*

**Challenge accepted.**

---

## Abstract

This document presents a rigorous, machine-checkable proof that the sky is blue. We reduce the claim to first principles, starting from the Standard Model of particle physics and culminating in a formally verified Lean 4 theorem. The proof has been checked by 10^47 CPU cycles and found to be sound, modulo the axioms of ZFC, the consistency of the universe, and the assumption that we are not living in a simulation (see Appendix Q: Simulation Hypothesis Considerations).

---

## 1. Problem Statement

**Claim:** The sky is blue.

**Formal Statement:**
```
∀ (observer : Human) (location : Paihia_NZ) (time : 2025-12-13T14:58:00+13:00),
  ¬ColorBlind(observer) ∧ ¬Cloudy(location, time) →
  Perceives(observer, Sky(location, time), Blue)
```

**Estimated Proof Complexity:** O(universe)

---

## 2. Scope Limitations

To make this proof tractable within the heat death of the universe, we constrain:

| Parameter | Constraint | Justification |
|-----------|------------|---------------|
| **Location** | Paihia, New Zealand | Author's current location; reduces proof to single point in spacetime |
| **Coordinates** | -35.2820° S, 174.0920° E | GPS precision ±3m; negligible for sky color |
| **Altitude** | Sea level ± 2m | Standing on beach, not levitating |
| **Time** | 2025-12-13T14:58:00+13:00 | Arbitrary choice; must be daytime |
| **Observer** | Average human | Not mantis shrimp (16 color receptors would complicate proof) |
| **Weather** | Clear sky | Clouds introduce cumulus-related edge cases |
| **Sobriety** | Sober | Psychedelics invalidate color perception axioms |

---

## 3. Axiom System

### 3.1 Physical Constants (Axiomatic)

```lean
axiom speed_of_light : ℝ := 299_792_458  -- m/s, CODATA 2018
axiom planck_constant : ℝ := 6.62607015e-34  -- J·s, exact by definition
axiom boltzmann_constant : ℝ := 1.380649e-23  -- J/K
axiom avogadro_number : ℝ := 6.02214076e23  -- mol⁻¹
axiom gravitational_constant : ℝ := 6.67430e-11  -- m³/(kg·s²)
axiom fine_structure_constant : ℝ := 0.0072973525693  -- dimensionless, the magic number
```

### 3.2 Astronomical Axioms

```lean
axiom earth_orbital_period : ℝ := 365.256363004  -- days
axiom earth_axial_tilt : ℝ := 23.44  -- degrees
axiom earth_radius : ℝ := 6_371_000  -- meters (mean)
axiom sun_surface_temp : ℝ := 5778  -- Kelvin
axiom earth_sun_distance : ℝ := 149_597_870_700  -- meters (1 AU)

-- J2000.0 Epoch: January 1, 2000, 11:58:55.816 UTC
axiom j2000_epoch : Timestamp := ⟨2000, 1, 1, 11, 58, 55, 816⟩
```

### 3.3 The Epoch Problem

We must establish Earth's position at the reference time. This requires:

```
Days since J2000.0 to 2025-12-13T14:58:00+13:00:
= 9478 days + 1 hour 58 minutes (after converting to UTC)
= 9478.0819444... days

Earth's orbital position θ = (360° / 365.256363004) × 9478.0819444
                          = 9339.847...°
                          = 9339.847 mod 360
                          = 219.847°

∴ Earth is approximately at 219.85° in its orbit (past vernal equinox)
```

### 3.4 Atmospheric Composition (Axiomatic)

```lean
structure Atmosphere where
  nitrogen : Float := 0.7808     -- N₂
  oxygen : Float := 0.2095       -- O₂
  argon : Float := 0.0093        -- Ar
  co2 : Float := 0.000417        -- CO₂ (417 ppm, 2025 estimate)
  water_vapor : Float            -- Variable, assume 0.01 for clear day
  other : Float := 0.000083      -- Ne, He, Kr, etc.

axiom paihia_atmosphere : Atmosphere := {
  water_vapor := 0.012  -- 1.2%, typical for NZ summer
}
```

---

## 4. Color Theory Foundations

### 4.1 Wavelength-Color Correspondence

```lean
inductive Color where
  | Violet    -- 380-450 nm
  | Blue      -- 450-495 nm  ← TARGET
  | Cyan      -- 495-520 nm
  | Green     -- 520-565 nm
  | Yellow    -- 565-590 nm
  | Orange    -- 590-625 nm
  | Red       -- 625-750 nm
  | Infrared  -- > 750 nm (invisible)
  | Ultraviolet -- < 380 nm (invisible)

def wavelength_to_color (λ : ℝ) : Option Color :=
  if λ < 380 then some .Ultraviolet
  else if λ < 450 then some .Violet
  else if λ < 495 then some .Blue      -- ← THE PROMISED LAND
  else if λ < 520 then some .Cyan
  else if λ < 565 then some .Green
  else if λ < 590 then some .Yellow
  else if λ < 625 then some .Orange
  else if λ < 750 then some .Red
  else if λ < 1000000 then some .Infrared
  else none  -- Gamma rays, probably
```

### 4.2 Human Color Perception Model

The human eye contains three types of cone cells:

```lean
structure ConeResponse where
  S : Float  -- Short wavelength (blue), peak ~420nm
  M : Float  -- Medium wavelength (green), peak ~530nm
  L : Float  -- Long wavelength (red), peak ~560nm

def cone_sensitivity (λ : ℝ) : ConeResponse := {
  S := gaussian λ 420 30   -- Blue cones
  M := gaussian λ 530 40   -- Green cones
  L := gaussian λ 560 50   -- Red cones
}

-- A color is perceived as "blue" when:
def perceives_as_blue (response : ConeResponse) : Bool :=
  response.S > response.M ∧
  response.S > response.L ∧
  response.S > 0.3  -- Above threshold
```

---

## 5. Rayleigh Scattering: The Core Mechanism

### 5.1 The Rayleigh Scattering Equation

Lord Rayleigh (1871) showed that the intensity of scattered light is:

```
I ∝ I₀ × (1 + cos²θ) / (2R²) × (2π/λ)⁴ × ((n²-1)/(n²+2))² × (d/2)⁶
```

**The critical insight:** Scattering intensity is proportional to **λ⁻⁴**

```lean
def rayleigh_scattering_intensity (λ : ℝ) (θ : ℝ) : ℝ :=
  let wavelength_factor := (1 / λ) ^ 4
  let angular_factor := 1 + (cos θ) ^ 2
  wavelength_factor * angular_factor

-- Blue light (450nm) vs Red light (650nm) scattering ratio:
-- (650/450)⁴ = 4.37
-- Blue light scatters 4.37× more than red light!
theorem blue_scatters_more_than_red :
  rayleigh_scattering_intensity 450 θ > 4 * rayleigh_scattering_intensity 650 θ := by
  sorry  -- Left as exercise for the reader (and by reader we mean supercomputer)
```

### 5.2 Why Not Violet?

**Objection:** Violet (380-450nm) scatters even MORE than blue. Why isn't the sky violet?

**Response:** Three factors:

1. **Solar spectrum:** The sun emits less violet than blue
2. **Atmospheric absorption:** Ozone absorbs some violet/UV
3. **Human eye sensitivity:** Our S-cones are less sensitive to violet

```lean
def solar_irradiance (λ : ℝ) : ℝ :=
  -- Planck's law for 5778K blackbody, simplified
  let peak := 502  -- nm (Wien's displacement law)
  gaussian λ peak 100  -- Approximation

def effective_sky_color (λ : ℝ) : ℝ :=
  solar_irradiance λ *
  rayleigh_scattering_intensity λ (π/2) *
  (cone_sensitivity λ).S

-- The convolution peaks around 470-480nm = BLUE
theorem effective_peak_is_blue :
  ∃ λ_peak ∈ (450, 495), ∀ λ, effective_sky_color λ_peak ≥ effective_sky_color λ := by
  sorry  -- Requires numerical integration
```

---

## 6. Solar Position Calculation

### 6.1 Computing Sun Position at Paihia, 2:58 PM

```lean
structure SolarPosition where
  azimuth : Float    -- Degrees from North
  altitude : Float   -- Degrees above horizon

def compute_solar_position
  (lat : Float) (lon : Float) (timestamp : Timestamp) : SolarPosition :=
  let days_since_j2000 := timestamp.days_since_j2000
  let mean_anomaly := 357.5291 + 0.98560028 * days_since_j2000
  let equation_of_center := 1.9148 * sin mean_anomaly +
                            0.0200 * sin (2 * mean_anomaly)
  let ecliptic_longitude := mean_anomaly + equation_of_center + 180 + 102.9372
  let declination := asin (sin ecliptic_longitude * sin 23.44)
  let hour_angle := compute_hour_angle lon timestamp
  let altitude := asin (sin lat * sin declination +
                        cos lat * cos declination * cos hour_angle)
  let azimuth := atan2 (sin hour_angle)
                       (cos hour_angle * sin lat - tan declination * cos lat)
  ⟨azimuth, altitude⟩

-- At Paihia (-35.28°, 174.09°) on 2025-12-13 at 14:58 NZDT:
def paihia_sun_position : SolarPosition :=
  compute_solar_position (-35.28) 174.09 ⟨2025, 12, 13, 14, 58, 0⟩

-- Result: Azimuth ≈ 335° (NNW), Altitude ≈ 72° (high in sky)
-- High sun = more atmosphere traversed = more scattering = BLUER sky
```

### 6.2 Atmospheric Path Length

```lean
def air_mass (solar_altitude : Float) : Float :=
  -- Kasten-Young formula (1989)
  1 / (sin solar_altitude + 0.50572 * (solar_altitude + 6.07995)^(-1.6364))

-- At 72° altitude:
-- air_mass ≈ 1.05 (nearly overhead, minimal path)
-- This means relatively pure Rayleigh scattering, minimal reddening
```

---

## 7. Photon Journey Simulation

To be truly rigorous, we simulate individual photons:

```lean
structure Photon where
  wavelength : Float  -- nm
  position : Vector3  -- meters from Earth center
  direction : Vector3 -- unit vector
  scattered : Bool

def simulate_photon_journey (p : Photon) : List ScatteringEvent :=
  let mean_free_path := compute_mfp p.wavelength (atmospheric_density p.position)
  let events := []
  while p.position.altitude > 0 && p.position.altitude < 100_000 do
    let distance_to_scatter := exponential_random mean_free_path
    p.position := p.position + p.direction * distance_to_scatter
    if random() < scattering_probability p.wavelength then
      let new_direction := rayleigh_scatter_direction p.direction
      events := events ++ [⟨p.position, p.wavelength, new_direction⟩]
      p.direction := new_direction
  events

-- Monte Carlo simulation with 10^9 photons
-- Results: 47.3% of photons reaching observer's eye have λ ∈ [450, 495] nm
-- Statistical confidence: 99.9999% (6σ)
```

---

## 8. The Final Proof

### 8.1 Proof Structure

```
                    ┌─────────────────────────────────────┐
                    │     AXIOMS (Standard Model, QED)    │
                    └───────────────┬─────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────┐
                    │   Lemma: Photons exist              │
                    │   Lemma: Atmosphere exists          │
                    │   Lemma: Human eyes exist           │
                    └───────────────┬─────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────┐
                    │   Theorem: Rayleigh scattering      │
                    │   occurs (λ⁻⁴ dependency)           │
                    └───────────────┬─────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────┐
                    │   Theorem: Blue light scatters      │
                    │   more than red light               │
                    └───────────────┬─────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────┐
                    │   Theorem: Scattered light reaches  │
                    │   observer from all sky directions  │
                    └───────────────┬─────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────┐
                    │   Theorem: Observer perceives       │
                    │   dominant wavelength as "blue"     │
                    └───────────────┬─────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────┐
                    │         ∴ THE SKY IS BLUE           │
                    │              Q.E.D.                 │
                    │                                     │
                    │   ✓ PROVEN                          │
                    │   (assuming physics works)          │
                    └─────────────────────────────────────┘
```

### 8.2 The Lean 4 Proof

```lean
import SkyIsBlue.Physics
import SkyIsBlue.Optics
import SkyIsBlue.Perception
import SkyIsBlue.Astronomy
import SkyIsBlue.AtmosphericScience
import SkyIsBlue.QuantumElectrodynamics

open Physics Optics Perception

/-- The main theorem: At 2:58 PM on December 13, 2025,
    in Paihia, New Zealand, a non-colorblind human observer
    looking at a cloudless sky will perceive it as blue. -/
theorem sky_is_blue
  (observer : Human)
  (h_not_colorblind : ¬ColorBlind observer)
  (h_location : observer.location = paihia)
  (h_time : observer.time = ⟨2025, 12, 13, 14, 58, 0, NZDT⟩)
  (h_clear : ¬Cloudy paihia ⟨2025, 12, 13, 14, 58, 0, NZDT⟩)
  (h_looking_up : observer.gaze_direction.altitude > 10)
  (h_sober : Sober observer)
  (h_eyes_open : EyesOpen observer)
  (h_not_underground : observer.altitude > -10)
  (h_not_in_space : observer.altitude < 100_000)
  (h_exists : ∃ observer, True)  -- Solipsism escape hatch
  : Perceives observer (Sky paihia ⟨2025, 12, 13, 14, 58, 0, NZDT⟩) Color.Blue := by

  -- Step 1: Establish that the sun is shining
  have h_daytime : IsDaytime paihia ⟨2025, 12, 13, 14, 58, 0, NZDT⟩ := by
    apply solar_position_implies_daytime
    exact compute_solar_position paihia.lat paihia.lon h_time
    norm_num

  -- Step 2: The sun emits photons across the visible spectrum
  have h_photons : EmitsVisibleLight Sun := sun_emits_blackbody_radiation

  -- Step 3: Photons travel to Earth
  have h_travel : PhotonsReachEarth Sun paihia h_time := by
    apply inverse_square_law
    exact earth_sun_distance
    exact h_photons

  -- Step 4: Rayleigh scattering occurs
  have h_scatter : ∀ λ, ScatteringIntensity λ ∝ λ⁻⁴ := rayleigh_1871

  -- Step 5: Blue scatters more
  have h_blue_wins : ∀ λ_blue λ_red,
    λ_blue ∈ blue_range → λ_red ∈ red_range →
    ScatteringIntensity λ_blue > 4 * ScatteringIntensity λ_red := by
    intros
    apply h_scatter
    norm_num

  -- Step 6: Scattered light reaches observer from sky (not sun direction)
  have h_sky_light : DominantWavelength (SkyLight paihia h_time) ∈ blue_range := by
    apply convolution_of_solar_spectrum_and_scattering
    exact h_scatter
    exact h_photons

  -- Step 7: Observer perceives blue
  have h_perceives : Perceives observer (Sky paihia h_time) Color.Blue := by
    apply human_color_perception
    exact h_not_colorblind
    exact h_sky_light
    exact h_sober
    exact h_eyes_open

  exact h_perceives

-- QED. The sky is blue. We did it.
-- Mass spectrometry confirms.
-- The simulation is satisfied.
```

---

## 9. Potential Objections & Rebuttals

### 9.1 "But what if we're in a simulation?"

Then the programmers chose to render the sky blue. The proof holds within the simulation's axioms. If the simulation has bugs, file a ticket with the universe maintainers.

### 9.2 "What about colorblind people?"

Excluded by precondition `h_not_colorblind`. Different proof required (see: `sky_is_grayish_blue.lean`).

### 9.3 "The sky is sometimes red/orange (sunset)"

Out of scope. This proof is constrained to 2:58 PM. For sunset, see `sunset_is_orange.lean` (estimated completion: 2027).

### 9.4 "What about at night?"

The sky is black at night. This is a separate theorem: `night_sky_is_black.lean`. Requires additional axioms about the absence of photons.

### 9.5 "What if I'm looking at the horizon?"

Gaze altitude > 10° is a precondition. Horizon has more atmospheric path length, shifting toward white/pale blue. Edge case excluded.

### 9.6 "You said 'sorry' in the proof!"

Every proof has axioms. Our `sorry` is simply "physics works as described." If this axiom is false, we have bigger problems than the color of the sky.

---

## 10. Computational Requirements

| Resource | Required | Available | Status |
|----------|----------|-----------|--------|
| CPU cycles | 10^47 | 10^20 (Earth's computers) | ❌ Need Dyson sphere |
| RAM | 10^15 TB | 10^11 TB (global) | ❌ Need Jupiter-brain |
| Time | 10^9 years | 0.0001 years | ❌ Need time dilation |

**Workaround:** Accept `sorry` as axiom. Proof reduces to 0.003 seconds.

---

## 11. Conclusion

We have rigorously proven, to within the precision of modern physics and the limits of formal verification, that the sky above Paihia, New Zealand, at 2:58 PM on December 13, 2025, appears blue to a sober, non-colorblind human observer with their eyes open who is standing on the ground and looking up.

**Proof Status:** ✓ VERIFIED (modulo physics)

---

## Appendices

- **Appendix A:** Full derivation of Rayleigh scattering from Maxwell's equations (427 pages)
- **Appendix B:** Proof that electrons exist (requires QED, 1,200 pages)
- **Appendix C:** Proof that the observer exists (requires Descartes, 1 page: "Cogito ergo sum")
- **Appendix D:** Proof that Paihia exists (requires Google Maps API)
- **Appendix E:** Proof that December 13, 2025 has occurred (requires axiom of time continuity)
- **Appendix F:** Proof that "blue" is a coherent concept (requires philosophy of language, ∞ pages)
- **Appendix Q:** Simulation hypothesis considerations (see: _The Matrix_, 1999)

---

## References

1. Rayleigh, Lord. (1871). "On the light from the sky, its polarization and colour."
2. Newton, I. (1704). *Opticks*.
3. Descartes, R. (1637). "I think therefore the sky is blue."

---

## Acknowledgments

- The Sun, for providing photons
- The atmosphere, for scattering them
- My eyes, for perceiving the result
- Claude, for typing it

---

```
████████╗██╗  ██╗███████╗    ███████╗██╗  ██╗██╗   ██╗
╚══██╔══╝██║  ██║██╔════╝    ██╔════╝██║ ██╔╝╚██╗ ██╔╝
   ██║   ███████║█████╗      ███████╗█████╔╝  ╚████╔╝
   ██║   ██╔══██║██╔══╝      ╚════██║██╔═██╗   ╚██╔╝
   ██║   ██║  ██║███████╗    ███████║██║  ██╗   ██║
   ╚═╝   ╚═╝  ╚═╝╚══════╝    ╚══════╝╚═╝  ╚═╝   ╚═╝

██╗███████╗    ██████╗ ██╗     ██╗   ██╗███████╗
██║██╔════╝    ██╔══██╗██║     ██║   ██║██╔════╝
██║███████╗    ██████╔╝██║     ██║   ██║█████╗
██║╚════██║    ██╔══██╗██║     ██║   ██║██╔══╝
██║███████║    ██████╔╝███████╗╚██████╔╝███████╗
╚═╝╚══════╝    ╚═════╝ ╚══════╝ ╚═════╝ ╚══════╝

              Q.E.D. ∎
```
