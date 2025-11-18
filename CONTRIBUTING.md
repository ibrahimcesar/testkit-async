# Contributing to testkit-async 🧰

Thank you for your interest in contributing!

## 🚧 Project Status

This project is in **early development**. We're building the foundation for practical async testing.

## 🤝 How to Contribute

### Reporting Issues

- **Bugs**: Describe issue, steps to reproduce
- **Feature Requests**: Explain use case and proposed API
- **Questions**: Use Discussions tab

### Code Contributions

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests
5. Run `cargo test` and `cargo clippy`
6. Submit a Pull Request

## 📋 Development Setup
```bash
# Clone
git clone https://github.com/yourusername/testkit-async
cd testkit-async

# Build
cargo build

# Run tests
cargo test

# Run examples
cargo run --example time_control

# Lint
cargo clippy
```

## 🎯 Priority Areas

- [ ] Mock clock implementation
- [ ] Test executor design
- [ ] Failure injector
- [ ] Async assertion macros
- [ ] Documentation and examples
- [ ] Runtime compatibility (tokio, async-std, smol)

## 📝 Code Style

- Follow Rust conventions (`cargo fmt`)
- Pass `cargo clippy`
- Add documentation for public APIs
- Include tests

## 🧪 Testing

- Add unit tests for all features
- Add integration tests for high-level APIs
- Test with multiple runtimes (tokio, async-std)

## 📜 License

By contributing, you agree that your contributions will be licensed under MIT OR Apache-2.0.
