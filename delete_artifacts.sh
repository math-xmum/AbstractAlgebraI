#!/bin/bash

# Replace with your repository information
OWNER="math-xmum"   # Could be your username or an organization
REPO_NAME="AbstractAlgebra"

# Ensure the GITHUB_TOKEN environment variable is set
if [ -z "$GITHUB_TOKEN" ]; then
  echo "Error: GITHUB_TOKEN environment variable is not set."
  exit 1
fi

# GitHub API URL to list artifacts
ARTIFACTS_URL="https://api.github.com/repos/$OWNER/$REPO_NAME/actions/artifacts"

# Get list of all artifacts
response=$(curl -s -H "Authorization: token $GITHUB_TOKEN" "$ARTIFACTS_URL")

# Extract artifact IDs using jq
artifact_ids=$(echo "$response" | jq -r '.artifacts[].id')

# Check if there are any artifact IDs
if [ -z "$artifact_ids" ]; then
  echo "No artifacts found."
  exit 0
fi

# Loop through each artifact ID and delete it
for artifact_id in $artifact_ids; do
  delete_url="https://api.github.com/repos/$OWNER/$REPO_NAME/actions/artifacts/$artifact_id"
  echo "Deleting artifact with ID: $artifact_id"

  # Delete the artifact
  curl -s -X DELETE -H "Authorization: token $GITHUB_TOKEN" "$delete_url"
done

echo "All artifacts have been deleted."

