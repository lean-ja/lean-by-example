/- # Lean のインストール方法

Lean および関連ツールのインストール方法を説明します。VSCode の Lean 4 拡張機能が自動的にインストールしてくれるのですが、ここではコマンドラインから手動で入れる場合の手順を説明します。

## Windows の場合

### PowerShell 7 のインストール

まずは使用しているシェルを確認します。[PowerShell 7](https://github.com/PowerShell/PowerShell) を使うことを推奨します。他のシェルでも Lean のインストール自体は可能ですが、Windows では PowerShell 7 を使うことが一般的であるためこのような手順を案内しています。

Windows PowerShell と PowerShell 7 以降は混同されがちですが、下記を実行して Major が 7 以上であれば PowerShell 7 です。

```powershell
$PSVersionTable.PSVersion
```

PowerShell 7 をインストールするには、次を実行します。

```powershell
winget install --id Microsoft.PowerShell --source winget
```

### git と curl のインストール

以下、全てのコマンドは PowerShell 7 で実行することを前提とすることにします。

Lean のインストールのためには `git` コマンドと `curl` コマンドが必要です。`git` はテキストのバージョン管理をするためのツールで、`curl` はデータを外部から取得したり、外部に送信したりするためのツールです。

それぞれインストール済みであるか、次のコマンドで確認します。

```powershell
git --version
curl --version
```

おそらく初期状態の Windows では `git` はインストールされていないと思います。以下のコマンドでインストールします。

```powershell
winget install --id Git.Git -e --source winget
```

`curl` コマンドはおそらく初めから入っていると思いますが、もし入っていない場合は次のコマンドでインストールします。

```powershell
winget install --id cURL.cURL --source winget
```

### elan のインストール

次に、Lean のバージョン管理ツールである `elan` をインストールします。次のコマンドでインストールできます。

```powershell
curl -O --location https://elan.lean-lang.org/elan-init.ps1
pwsh `
  -ExecutionPolicy Bypass `
  -f elan-init.ps1 `
  -NoPrompt:$True
Remove-Item elan-init.ps1
```

実行後、`elan` コマンドが使えるようになったか確認します。

```powershell
elan --version
```

### Lean と lake のインストール

次に、Lean（と同梱されている `lake`）をインストールします。`stable` を指定することで、最新の安定版をインストールできます。

```powershell
elan toolchain install stable
```

もし、`-rc` 系も含めた最新版をインストールしたい場合は、次のようにします。

```powershell
elan toolchain install beta
```

終わったら、Lean と `lake` のバージョンを確認します。

```powershell
lean --version
lake --version
```

## Linux の場合

だいたい Windows での手順と同様です。シェルは `bash` を使用することを想定して手順を書きます。

### git と curl のインストール

まず、`git` と `curl` がインストール済みであるか確認します。

```bash
git --version
curl --version
```

インストールされていなければインストールします。

```bash
sudo apt update
sudo apt install -y git curl
```

### elan のインストール

次に `elan` をインストールします。

```bash
curl -O --location https://elan.lean-lang.org/elan-init.sh
sh elan-init.sh -y --default-toolchain stable
rm elan-init.sh
```

終わったら `elan` コマンドが使えるようになったか確認します。

```bash
elan --version
```

### Lean と lake のインストール

次に、Lean（と同梱されている `lake`）をインストールします。`stable` を指定することで、最新の安定版をインストールできます。

```powershell
elan toolchain install stable
```

もし、`-rc` 系も含めた最新版をインストールしたい場合は、次のようにします。

```powershell
elan toolchain install beta
```

終わったら、Lean と `lake` のバージョンを確認します。

```powershell
lean --version
lake --version
```
-/
