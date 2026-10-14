# Continuous graph connectors

The current drawing overlaps a closed stroke with closed collars.
The exposed boundary can switch between curves with different tangents.
The scope specimen gives a finite counterexample at its fork-to-target connector.

## Representation

A connector body contains two open cubic chains with the same direction.
The constructor reserves the flare necks before it samples either side.
Each neck shares its anchor and handle with its adjoining flare.
The outline follows both chains and closes across their surface cuts.
The SVG writer emits one closed path for each connector.
The kit owns the paired-edge ribbon representation.
The view owns route docking, integer sampling and graph style.

## Proof placement

The concept is `initial-algebras-folds`.
The consumer is R14's graph drawing under decisions row 334(3).
These are tool laws, not machine registry claims.

| Obligation | Role | Consumer | Observation and assumptions |
| --- | --- | --- | --- |
| `Connector.Cache.valid_empty` | Cache premise | Fresh graph drawing | The empty table contains no incorrect outline |
| `Connector.cached_eq` | Cache observation | Graph drawing across frames | A valid cache answers the request's exact integer outline |
| `Connector.cached_valid` | Cache invariant | The next frame | Lookup or insertion retains the request-to-outline relation |
| `SceneBridge.from_cubic` | Record conversion | Connector and peg drawing | Every local cubic returns with identical integer controls |
| `SceneBridge.cubic_from` | Record conversion | Connector and peg drawing | Every kit cubic returns with identical integer controls |

The new cache key includes both docking offsets and radii.
The drawing normalizes route coordinates before it requests an outline.
The drawing applies its translation after the cache lookup.
These laws establish no curve simplicity, clearance, rasterization or machine behaviour.
The geometry receipt places its own neck and ribbon laws before their proofs.
The shared record bridge imports integer scene coordinates without importing peg geometry.

## Finite checks

The SVG gate rejects separate body and collar paths for one connector.
The gate checks all intended side joins for position and oriented tangent agreement.
The gate excludes the two transverse surface caps.
Close-up renders inspect the scope counterexample and fork, join and animated contacts.
The existing XML, path grammar and reference checks still apply.
