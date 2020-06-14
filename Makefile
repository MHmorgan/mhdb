all : prepare

install :
	cargo install --path .

test : export CARGO_INCREMENTAL=0
test : export RUSTFLAGS=-Zprofile -Ccodegen-units=1 -Copt-level=0 -Clink-dead-code -Coverflow-checks=off -Zpanic_abort_tests -Cpanic=abort
test :
	rm -f ./target/debug/deps/*.gcda
	cargo test --all-features

coverage : test
	grcov ./target/debug/ -s . -t html --llvm --branch --ignore-not-existing -o ./target/debug/coverage/
	xdg-open ./target/debug/coverage/index.html

check-release :
	# cargo rustc --release --all-features -- -F warnings -F unused -W rustdoc -D deprecated-in-future -W elided-lifetimes-in-paths -W keyword-idents -W macro-use-extern-crate -W meta-variable-misuse -D missing-copy-implementations -D missing-crate-level-docs -D missing-debug-implementations -W non-ascii-idents -W single-use-lifetimes -W trivial-casts -W trivial-numeric-casts -D unused-extern-crates -D unused-results
	cargo rustc --release --all-features -- -F warnings -W rustdoc -D deprecated-in-future -W elided-lifetimes-in-paths -W keyword-idents -W macro-use-extern-crate -W meta-variable-misuse -D missing-copy-implementations -D missing-crate-level-docs -W non-ascii-idents -W single-use-lifetimes -W trivial-casts -W trivial-numeric-casts -D unused-extern-crates
	cargo test -q --release
	cargo audit

doc :
	cargo doc --offline --no-deps --open

# Prepare for release
prepare :
	cargo fix --workspace --edition-idioms --release
	cargo clippy --verbose
