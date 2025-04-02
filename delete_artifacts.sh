#!/bin/bash

# Your GitHub repository details
REPO_OWNER="math-xmum"     # Replace with your repository owner
REPO_NAME="AbstractAlgebra"       # Replace with your repository name
TOKEN="$GITHUB_TOKEN"            # GitHub token with repo access

# Get a list of artifacts and their IDs
ARTIFACTS=$(curl -H "Authorization: token $TOKEN" \
              -H "Accept: application/vnd.github.v3+json" \
              "https://api.github.com/repos/$REPO_OWNER/$REPO_NAME/actions/artifacts" | jq '.artifacts[] | {id: .id, name: .name}')

# Iterate over each artifact and delete it
echo "$ARTIFACTS" | jq -c '.[]' | while read artifact; do
    ARTIFACT_ID=$(echo "$artifact" | jq -r '.id')
    ARTIFACT_NAME=$(echo "$artifact" | jq -r '.name')
    echo "Deleting artifact: $ARTIFACT_NAME (ID: $ARTIFACT_ID)"
    curl -X DELETE -H "Authorization: token $TOKEN" \
         -H "Accept: application/vnd.github.v3+json" \
         "https://api.github.com/repos/$REPO_OWNER/$REPO_NAME/actions/artifacts/$ARTIFACT_ID"
done
